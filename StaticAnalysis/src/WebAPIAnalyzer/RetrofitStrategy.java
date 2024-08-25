package WebAPIAnalyzer;


import cg.CallGraphUtils;
import dataflow.*;
import fj.Hash;
import javafx.scene.Scene;
import jdk.internal.org.objectweb.asm.AnnotationVisitor;
import org.json.JSONObject;
import soot.*;
import soot.jimple.*;
import soot.jimple.internal.JIdentityStmt;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.jimple.internal.JimpleLocalBox;
import soot.tagkit.*;
import util.Log;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import javax.swing.text.html.HTML.Tag;

import static cg.CallGraphUtils.getAllFields;
import static dataflow.AbstractDataFlow.*;


/**
 * @program: Ditto
 * @description:  The API extraction strategy for Retrofit API
 **/
public class RetrofitStrategy extends APIURLStrategy{

    public final HashSet<String> requestURLs = new HashSet<>();

    public String URLPath = "";
    public String httpmethod = "";

    public MoshiGSONStrategy moshiGSONStrategy;

    public RetrofitStrategy(APIAnalyzer analyzer, MoshiGSONStrategy moshiGSONStrategy){
        super(analyzer);
        this.moshiGSONStrategy = moshiGSONStrategy;
    }


   @Override
    public void extract(Snippet snippet){
        // Find the Retrofit URL from the call stack, along with the interface parameters
        if(this.analyzer.DUSSAPIs.keySet().contains(snippet.getAPICallSite())) return;
        Stmt invokeUnit = (Stmt) snippet.getAPIinvoke();
        if(!invokeUnit.containsInvokeExpr())
           return;


        boolean hasURLinRequest = false;
        boolean hasURLinResponse = false;

        SootMethod retrofitAPI = snippet.getAPICallSite().callee;
        int urlObjectIndex = -1;
        for(Tag tag : retrofitAPI.getTags()){
            if(tag instanceof VisibilityAnnotationTag){
                VisibilityAnnotationTag annotationTag = (VisibilityAnnotationTag) tag;
                for(AnnotationTag at : annotationTag.getAnnotations()){
                    for(AnnotationElem ae : at.getElems()){
                        AnnotationStringElem ase = (AnnotationStringElem) ae;
                        this.URLPath = ase.getValue();
                    }
                    if(at.getType().contains("POST")){
                        this.httpmethod="POST";
                    }else if(at.getType().contains("GET")){
                        this.httpmethod = "GET";
                    }else if(at.getType().contains("PATCH")){
                        this.httpmethod = "PATCH";
                    }else if(at.getType().contains("DELETE")){
                        this.httpmethod = "DELETE";
                    }else if(at.getType().contains("PUT")){
                        this.httpmethod = "PUT";
                    }
                }
            }
            if(tag instanceof VisibilityParameterAnnotationTag){
                VisibilityParameterAnnotationTag pTag = (VisibilityParameterAnnotationTag) tag;
                int p_count = 0;
                for(VisibilityAnnotationTag vat2: pTag.getVisibilityAnnotations()){
                    p_count+=1;
                    if(vat2==null)
                        continue;
                    for(AnnotationTag pat : vat2.getAnnotations()){
                        for(AnnotationElem pae : pat.getElems()){
                            if(pae instanceof AnnotationStringElem){
                                AnnotationStringElem pase = (AnnotationStringElem) pae;
                                if(pase.getValue().toLowerCase().contains("url")){
                                    // Get the parameter position from the annotation
                                    logger.info("Parameter index:"+p_count);
                                    urlObjectIndex = p_count;
                                    hasURLinRequest = true;
                                }
                            }
                        }
                    }
                }
            }
        }

        //Backward data flow analyzes each parameter of the api function to determine whether it is reachable by the data declaration of the URL type
        if(urlObjectIndex == -1){
            if(!invokeUnit.containsInvokeExpr())
                return;
            for(int i =0; i<invokeUnit.getInvokeExpr().getArgCount();i++){
                ValueBox pValue = invokeUnit.getInvokeExpr().getArgBox(i);
                if(findURLObject_backward(snippet.getLastCaller(),snippet.getAPIinvoke(),pValue,snippet.callstacks,true))
                    hasURLinRequest = true;
            }
        }else{
            // Provenance analysis
            ValueBox pValue = invokeUnit.getInvokeExpr().getArgBox(urlObjectIndex);
            hasURLinRequest = provenanceAnalysis(snippet.getLastCaller(), snippet.getAPIinvoke(), pValue, snippet.callstacks,true);
        }

        if(hasURLinRequest){
            // Start analyzing the Response, find the callback function, and analyze the parameter types of the forward data flow
            SootMethod sootMethod = snippet.getLastCaller();
            Body body = sootMethod.retrieveActiveBody();
            for(Unit unit : body.getUnits()){
                Stmt stmt = (Stmt) unit;
                for(ValueBox valueBox : stmt.getUseBoxes()){
                    if(valueBox.getValue() instanceof NewExpr){
                        NewExpr newExpr = (NewExpr) valueBox.getValue();
                        SootClass sc = newExpr.getBaseType().getSootClass();
                        if(CallGraphUtils.isImplementInterface(sc,"io.reactivex.Observer")){
                            // Technically, we should start with the onNext interface, but since the programming specification exists, we'll just go straight to onSuccess
                            for(SootMethod sm : sc.getMethods()){
                                if(sm.getName().toLowerCase().contains("success")){
                                    SootMethod callback  = sm;
                                    this.callBack.add(callback);
                                    if(analyzeResponseCallback(callback)){
                                        hasURLinResponse = true;
                                    };
                                }
                            }
                        }
                    }
                }
            }
        }
       recordResult(snippet);
    }

    private boolean analyzeResponseCallback(SootMethod sootMethod){
        // Forward data flow analysis to see if any URL type variables are contaminated. 
        // Determine whether the contaminated variable is: (1) a Field with a URL; (2) There is a JSON parsing process and URL field extraction; (3) String URL conversion operation
        Analyze myAnalyze = new Analyze() {

            public boolean flag = false;

            @Override
            public boolean caseAnalyze(Unit unit, SootMethod method, List<CallSite> callStack, HashSet<Point> res, ValueBox taintValueBox) {
                if(unit instanceof AssignStmt){
                    AssignStmt assignStmt = (AssignStmt) unit;
                    if(!assignStmt.containsInvokeExpr()){
                        if(!assignStmt.containsFieldRef()){
                            if(!assignStmt.containsArrayRef()){
                                String transferClass = assignStmt.getRightOp().getType().toString();
                                if(!isSystemClassName(transferClass)){
                                    SootClass sootClass = Scene.v().getSootClass(transferClass);
                                    HashSet<String> fileds = (HashSet<String>) getAllFields(sootClass);
                                    if(containsURLField(fileds)){
                                        this.flag = true;
                                        return true;
                                    }

                                }
                            }
                        }
                    }
                }
                return false;
            }

            @Override
            public boolean returnStatus() {
                return flag;
            }
        };
        for(int index = 0; index < sootMethod.getParameterCount(); index++){
            if(findURLObject_forward(sootMethod,null,null,0)) return true;
        }
        return false;
    }

    public boolean containsURLField(HashSet<String> fieldNames){
        if(fieldNames.isEmpty())
            return false;
        boolean hasURLField = false;
        for(String name : fieldNames){
            String fieldname = name.substring(name.indexOf("#"));
            if (fieldname.toLowerCase().contains("url")||fieldname.toLowerCase().contains("link")){
                shortURLFields.add(name);
                hasURLField = true;
            }
        }
        return hasURLField;
    }

}
