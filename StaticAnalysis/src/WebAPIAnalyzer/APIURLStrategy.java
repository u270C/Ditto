package WebAPIAnalyzer;

import cg.CallGraphUtils;
import dataflow.*;
import fj.data.hlist.HPre;
import javafx.scene.Scene;
import okhttp3.HttpUrl;
import soot.*;
import soot.jimple.*;
import soot.jimple.internal.JVirtualInvokeExpr;
import util.Log;

import java.io.StringReader;
import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import static cg.CallGraphUtils.getAllFields;
import static dataflow.AbstractDataFlow.*;


/**
 * @program: Ditto
 * @description:  The basic strategy of analyzing a Web API, specially whether it is an DUSS-related. 
 **/
public class APIURLStrategy {

    APIAnalyzer analyzer;

    public final HashSet<SootMethod> callBack = new HashSet<>();

    public final HashSet<SootMethod> URLGetter = new HashSet<>();

    public final HashSet<String> shortURLFields = new HashSet<>();

    public boolean hasURLinRequest = false;
    public boolean hasURLinResponse = false;

    /**
     * This class inherits the data flow analysis interface, 
     * it implements a customized DFG for find the provenance method of an `URL object`.
     */
    public class URLGetterAnalyze implements Analyze {

        public boolean flag;

        URLGetterAnalyze(){
            this.flag = false;
        }

        @Override
        public boolean caseAnalyze(Unit unit, SootMethod method, List<CallSite> callStack, HashSet<Point> res, ValueBox taintValueBox) {
            if(unit instanceof AssignStmt){
                AssignStmt assignStmt = (AssignStmt) unit;
                if(assignStmt.containsInvokeExpr()){
                    SootClass declaringClass = assignStmt.getInvokeExpr().getMethod().getDeclaringClass();
                    if(!isSystemClass(declaringClass)){
                        URLGetter.add(assignStmt.getInvokeExpr().getMethod());
                        this.flag = true;
                        return true;
                    }else if(isURL2String(assignStmt)){
                        URLGetter.add(assignStmt.getInvokeExpr().getMethod());
                        this.flag = true;
                        return true;
                    }
                }
            }
            return false;
        }

        @Override
        public boolean returnStatus() {
            return this.flag;
        }
    };

    /**
     * This class inherits the data flow analysis interface, 
     * it implements a customized DFG for find the whether an object is URL-type.
     * We determine whether it is an URL-type object by: Class Name, String value.
     */
    public class URLObjectAnalyze implements Analyze {

        public boolean flag;

        URLObjectAnalyze(){
            this.flag = false;
        }

        @Override
        public boolean caseAnalyze(Unit unit, SootMethod method, List<CallSite> callStack, HashSet<Point> res, ValueBox taintValueBox) {

            // Determine whether a TaintValue is a URL object: 
            // 1. The value of this object comes from the system interface, such as Uri.toStirng, URL.getURL, WebView.getURL 
            // 2. The object is related to the key-value data structure object, and the Key contains the URL

            if(unit instanceof AssignStmt){
                AssignStmt assignStmt = (AssignStmt) unit;
                if(assignStmt.containsInvokeExpr()){
                    SootClass declaringClass = assignStmt.getInvokeExpr().getMethod().getDeclaringClass();
                    if(isURL2String(assignStmt)){
                        if(declaringClass.toString().equals("android.net.Uri") || declaringClass.toString().equals("java.net.URL")){
                            provenanceAnalysis(method,unit,assignStmt.getDefBoxes().get(0),callStack,false);
                        }else{
                            URLGetter.add(assignStmt.getInvokeExpr().getMethod());
                        }
                        logger.info("Find URL type variable from: "+assignStmt.getInvokeExpr().getMethod().getSignature());
                        Log.write("Find URL type variable from: "+assignStmt.getInvokeExpr().getMethod().getSignature());
                        flag = true;
                        return true;
                    }
                }
            }
            Stmt stmt = (Stmt) unit;
            ArrayList<String> sinks = new ArrayList<>();
            sinks.add("<java.util.HashMap: java.lang.Object put(java.lang.Object,java.lang.Object)>"); //  hashMapSink
            sinks.add("<org.json.JSONObject: org.json.JSONObject put(java.lang.String, java.lang.Object)>"); // jsonSink
//                String gsonSink = "";
            if(stmt.containsInvokeExpr()){
                String invokeMethodName = stmt.getInvokeExpr().getMethod().toString();
                if(sinks.contains(invokeMethodName)){
                    JVirtualInvokeExpr invokePutRequest = (JVirtualInvokeExpr) stmt.getInvokeExpr();
                    Value keyValue = invokePutRequest.getArg(0);
                    ValueBox valBox = invokePutRequest.getArgBox(1);
                    if(keyValue instanceof Constant){
                        Constant key = (Constant) keyValue;
                        if (key.toString().toLowerCase().contains("url")){
                            provenanceAnalysis(method,unit,valBox,callStack,false);
                            this.flag = true;
                        }
                    }else{
                        System.out.println("Non-constant key value, need backward analysis."+keyValue.toString());
                    }
                    if(!this.flag) findURLObject_backward(method, unit, valBox, callStack,false);
                }
                // The rest is handled by ordinary data flow analysis
            }
            return false;
        }

        @Override
        public boolean returnStatus() {
            return this.flag;
        }
    }

    /**
     * Determine the type conversion of the returned data, 
     * and if it is converted to another class, 
     * and the class is not of type JSON, then Field analysis is performed.
     */
    public class URLFieldAnalyze implements Analyze{

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
            return this.flag;
        }
    }

    public BackwardDataFlow getterProvenance = new BackwardDataFlow(new URLGetterAnalyze());

    public BackwardDataFlow backwardURLFinder = new BackwardDataFlow(new URLObjectAnalyze());

    public ForwardDataFlow forwardURLFinder = new ForwardDataFlow(new URLFieldAnalyze());

    public APIURLStrategy(APIAnalyzer analyzer){
        this.analyzer = analyzer;
    }

    public boolean extract(String potentialURL, String httpMethod, String libraryName, String path){

        return false;
    }

    /**
     * Follow the basic API URL construction call stacks to check whether it is DUSS-related.
     * @param snippet, the code snippet from an entrypoint to POI.
     */
    public void extract(Snippet snippet){
        if(this.analyzer.DUSSAPIs.keySet().contains(snippet.getAPICallSite())) return;
        Stmt invokeUnit = (Stmt) snippet.getAPIinvoke();
        if(!invokeUnit.containsInvokeExpr())
            return;

        SootMethod API = snippet.getAPICallSite().callee;

        for(CallSite cs : snippet.callstacks){
            if(cs.callee==null)
                continue;
            String classType = cs.callee.getDeclaringClass().getName();
            String methodName = cs.callee.getName();
            if(classType.contains("bitly")&&methodName.equals("shorten")){
                this.URLGetter.add(cs.callee);
                this.hasURLinRequest = true;
                this.hasURLinResponse = true;
                recordResult(snippet);
                return;
            } else if (classType.contains("branch")||classType.contains("appsflyer")) {
                if(methodName.toLowerCase().contains("generatelink")){
                    this.URLGetter.add(cs.callee);
                    this.hasURLinRequest = true;
                    this.hasURLinResponse = true;
                    recordResult(snippet);
                    return;
                }
            }
        }

        for(int i =0; i<invokeUnit.getInvokeExpr().getArgCount();i++){
            ValueBox pValue = invokeUnit.getInvokeExpr().getArgBox(i);
            if(findURLObject_backward(snippet.getLastCaller(),snippet.getAPIinvoke(),pValue,snippet.callstacks,true))
                hasURLinRequest = true;
        }

        if(hasURLinRequest){
            SootMethod sootMethod = snippet.getLastCaller();
            // The return value, which defaults to the API, is the result of the network request response
            if(invokeUnit instanceof AssignStmt){
                ValueBox assignedBox = ((AssignStmt) invokeUnit).getLeftOpBox();
                if(findURLObject_forward(sootMethod,invokeUnit,assignedBox,0))
                    hasURLinResponse = true;
            }
        }

        recordResult(snippet);

    }

    public boolean isValidURL(String urlString) {
        if (HttpUrl.parse(urlString) == null) {
            return false;
        } else {
            return true;
        }
    }

    public boolean isURL2String(Unit unit){
        Stmt stmt = (Stmt) unit;
        if(stmt.containsInvokeExpr()){
            InvokeExpr invokeExpr = stmt.getInvokeExpr();
            if(invokeExpr.getMethodRef().tryResolve()==null)
                return false;
            String classNameOfInvokeExpr = invokeExpr.getType().toString();
            String methodNameOfInvokeExpr = invokeExpr.getMethod().getName();
            if(classNameOfInvokeExpr.equals("android.webkit.WebView") && methodNameOfInvokeExpr.equals("getUrl")){
                return true;
            } else if (classNameOfInvokeExpr.equals("android.net.Uri") && methodNameOfInvokeExpr.equals("toString")){
                return true;
            } else if (classNameOfInvokeExpr.equals("java.net.URL") && methodNameOfInvokeExpr.equals("getUrl")) {
                return true;
            }
        }
        return false;
    }

    public boolean isURLClass(SootClass sootClass){
        if(sootClass.getName().equals("android.net.Uri") || sootClass.getName().equals("java.net.URL"))
            return true;
        return false;
    }

    public boolean containsURLField(HashSet<String> fieldNames){
        if(fieldNames.isEmpty())
            return false;
        boolean hasURLField = false;
        for(String name : fieldNames){
            String fieldname = name.substring(name.indexOf("#"));
            if (fieldname.toLowerCase().contains("url")){
                shortURLFields.add(name);
                hasURLField = true;
            }
        }
        return hasURLField;
    }

    public boolean provenanceAnalysis(SootMethod currentMethod, Unit invokeUnit, ValueBox valueBox, List<CallSite> callStacks, boolean shouldRemoveLast){
        getterProvenance.startBackward();
        if(shouldRemoveLast){
            getterProvenance.inter_backward_dataflow(currentMethod,invokeUnit,valueBox,callStacks.size()-2,getterProvenance.copyAndRemoveLast(callStacks));
        }else{
            getterProvenance.inter_backward_dataflow(currentMethod,invokeUnit,valueBox,callStacks.size()-1,new ArrayList<>(callStacks));
        }
        return getterProvenance.getAnalyzer().returnStatus();
    }

    public boolean findURLObject_backward(SootMethod sootMethod, Unit unit, ValueBox valueBox, List<CallSite> callStacks, boolean shouldRemoveLast){
        // Given an invokeUnit and the corresponding parameter Box (as the Request Body), backward analysis of whether the Request Body consists of an Object of type URL
        backwardURLFinder.startBackward();
        if(shouldRemoveLast){
            backwardURLFinder.inter_backward_dataflow(sootMethod,unit,valueBox,callStacks.size()-2,backwardURLFinder.copyAndRemoveLast(callStacks));
        }else{
            backwardURLFinder.inter_backward_dataflow(sootMethod,unit,valueBox,callStacks.size()-1,new ArrayList<>(callStacks));
        }
        return backwardURLFinder.getAnalyzer().returnStatus();
    }

    public boolean findURLObject_forward(SootMethod sootMethod, Unit unit, ValueBox valueBox, int paramIndex){
        // Given a statement, forward analysis of whether the Response Body consists of an Object of type URL.
        // Note that: Our experience shows that the call depth is generally no more than 5 layers.
        forwardURLFinder.setMAX_DEPTH(5);
        forwardURLFinder.inter_forward_dataflow(sootMethod,unit,valueBox,paramIndex,0,new ArrayList<>());
        return false;
    }

    public void recordResult(Snippet snippet){
        if( (hasURLinRequest && hasURLinResponse)) {
            String result = "{URLGetter="+this.URLGetter.toString()+",CallBack="+this.callBack.toString()+",ResponseFields="+this.shortURLFields+"}";
            this.analyzer.DUSSAPIs.put(snippet.getAPICallSite(),result);
        }else if (snippet.getPOIMethod().getName().toLowerCase().contains("shorturl")){
            String result = "{URLGetter="+this.URLGetter.toString()+",CallBack="+this.callBack.toString()+",ResponseFields="+this.shortURLFields+"}";
            this.analyzer.DUSSAPIs.put(snippet.getAPICallSite(),result);
        }
    }


}
