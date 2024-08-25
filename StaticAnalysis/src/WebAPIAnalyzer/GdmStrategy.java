package WebAPIAnalyzer;

import cfg.CfgFactory;
import cg.CallGraphUtils;
import dataflow.*;
import javafx.scene.Scene;
import soot.*;
import soot.jimple.*;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.options.Options;
import soot.toolkits.graph.BriefUnitGraph;
import soot.util.Cons;
import util.Log;

import java.util.*;

import static cg.CallGraphUtils.getAllFields;
import static dataflow.AbstractDataFlow.*;

/**
 * @program: Ditto
 * @description:  The API extraction strategy for GdmOceanNet
 **/
public class GdmStrategy extends APIURLStrategy{

    public GdmStrategy(APIAnalyzer analyzer){
        super(analyzer);
    }

    public void extract(Snippet snippet){
        if(this.analyzer.DUSSAPIs.containsKey(snippet.getAPICallSite())) return;
        // Step1: Look for the path to add the Request Body on the POI path
        String putRequest_sig = "<com.alibaba.aliexpress.gundam.ocean.netscene.GdmNetScene: void putRequest(java.lang.String,java.lang.String)>";
        SootMethod lstCaller = snippet.getLastCaller();
        HashSet<List<CallSite>> accesspaths = new HashSet<>();
        boolean hasURLinRequest = false;
        List<CallSite> path2AddURL = new ArrayList<>();
        if(CallGraphUtils.dfsV2(Scene.v().getCallGraph(),lstCaller,putRequest_sig,3, accesspaths)){
            for(List<CallSite> path: accesspaths){
                // Step2：Extract the parameter Object from the Request Body and analyze whether it is a URL type one by one
                Unit invokeUnit = path.get(path.size()-1).invokeUnit;
                Expr invokeexpre = ((Stmt) invokeUnit).getInvokeExpr();
                if(invokeexpre instanceof JVirtualInvokeExpr){
                    JVirtualInvokeExpr invokePutRequest = (JVirtualInvokeExpr) invokeexpre;
                   // Note： argBoxes[0].getValue().toString() is the key of request body
                    Value keyValue = invokePutRequest.getArg(0);
                    if(keyValue instanceof Constant){
                        // Check that the semantics of the key includes the URL
                        Constant key = (Constant) keyValue;
                        if (key.toString().toLowerCase().contains("url")){
                            hasURLinRequest = true;
                            path2AddURL.addAll(path);
                            // Track the Define and Use chain of the value
                            ValueBox valueObject = invokePutRequest.getArgBox(1);
                            List<CallSite> callStacks = new ArrayList<>();
                            for(CallSite cs : snippet.callstacks){
                                callStacks.add(cs);
                                if(cs.callee!=null && cs.callee.equals(path2AddURL.get(0).callee)){
                                    path2AddURL.remove(0);
                                    break;
                                }
                            }
                            callStacks.addAll(path2AddURL);
                            SootMethod currentMethod = path.get(path.size()-1).caller;
                            callStacks.remove(callStacks.size()-1);
                            getterProvenance.inter_backward_dataflow(currentMethod,invokeUnit,valueObject,callStacks.size()-1,callStacks);
                        }
                    }else{
                        // Trace back, and extract the possible source string of the Key。
                        System.out.println("Non-constant key value, need backward analysis."+keyValue.toString());
                    }
                }else Log.write("Wrong expression.");
            }
        }

        boolean hasURLinResponse = false;
        if(hasURLinRequest){
            // Step3: Find the Response Body for an Object of the URL type
            ValueBox businessCallback;
            snippet.getLastCaller();
            if(snippet.getPOIMethod().getName().equals("asyncRequest")){
                // Find the instance object of CallBack through stain analysis.
                CallSite targetSite = snippet.getAPICallSite();
                businessCallback = ((Stmt) targetSite.invokeUnit).getInvokeExpr().getArgBox(0);
                List<CallSite> callStacks = new ArrayList<>(snippet.callstacks);
                callStacks.remove(callStacks.size()-1);
                if(findCallBackDataFlow(targetSite.caller,targetSite.invokeUnit,businessCallback,callStacks.size()-1,callStacks)){
                    for(SootMethod callback : this.callBack){
                        // Step4: Analyze response Callback function
                        if(analyzeResponse(callback)){
                            hasURLinResponse = true;
                        }
                    }
                }

            }
        }

        recordResult(snippet);
    }

    private boolean analyzeResponse(SootMethod sootMethod){

        // Forward data flow analysis to see if any URL type variables are contaminated. 
        // Determine whether the contaminated variable is: (1) a Field with a URL; (2) There is a JSON parsing process and URL field extraction; (3) String URL conversion operation
        Analyze myAnalyze = new Analyze() {

            public boolean flag = false;

            @Override
            public boolean caseAnalyze(Unit unit, SootMethod method, List<CallSite> callStack, HashSet<Point> res, ValueBox taintValueBox) {
                // Determine the type conversion of the returned data, and if it is converted to another class, and the class is not of type JSON, then Field analysis is performed.
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
                                        flag = true;
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

        Body body = sootMethod.retrieveActiveBody();
        for(Unit unit:body.getUnits()){
            if(unit instanceof AssignStmt){
                AssignStmt assignStmt = (AssignStmt) unit;
                if(assignStmt.containsInvokeExpr() && assignStmt.getInvokeExpr().getMethod().getSignature().equals("<com.aliexpress.service.task.task.BusinessResult: java.lang.Object getData()>")){
                    ValueBox begin = assignStmt.getDefBoxes().get(0);
                    findURLObject_forward(sootMethod,unit,begin,0);
                }
            }
        }
        return forwardURLFinder.getFindFlag();
    }

    // find the response callback method
    private boolean findCallBackDataFlow(SootMethod method, Unit endUnit, ValueBox endValueBox, int depth, List<CallSite> callStack) {

        Analyze callbackAnalyze = new Analyze() {
            public boolean flag = false;

            public boolean returnStatus(){
                return flag;
            }

            @Override
            public boolean caseAnalyze(Unit unit, SootMethod method, List<CallSite> callStack, HashSet<Point> res, ValueBox taintValueBox) {
                if(unit instanceof AssignStmt){
                    AssignStmt assignStmt = (AssignStmt) unit;
                    Value rightOP = assignStmt.getRightOp();
                    if(rightOP instanceof NewExpr){
                        NewExpr newExpr = (NewExpr) rightOP;
                        SootClass sc = newExpr.getBaseType().getSootClass();
                        if(sc.implementsInterface("com.aliexpress.service.task.task.BusinessCallback")){
                            System.out.println("Find Callback Instance: "+sc.getName());
                            SootMethod callback = sc.getMethodByName("onBusinessResult");
                            if(!callBack.contains(callback))
                                callBack.add(callback);
                            flag = true;
                            return true;
                        }
                    }
                }
                return false;
            }
        };

        BackwardDataFlow bdf = new BackwardDataFlow(callbackAnalyze);
        bdf.inter_backward_dataflow(method,endUnit,endValueBox,depth,callStack);
        return callbackAnalyze.returnStatus();
    }

}
