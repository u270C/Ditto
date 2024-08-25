package WebAPIAnalyzer;

import dataflow.CallSite;
import javafx.scene.Scene;
import soot.*;
import soot.jimple.Stmt;

import javax.swing.text.html.Option;
import java.util.HashSet;

/**
 * @program: Ditto
 * @description:  The API extraction strategy for Okhttp3
 **/
public class OkHttpStrategy extends APIURLStrategy{

    public OkHttpStrategy(APIAnalyzer analyzer){
        super(analyzer);
    }

    public void extract(Snippet snippet){
        if(this.analyzer.DUSSAPIs.keySet().contains(snippet.getAPICallSite())) return;
        CallSite apiCallSite = snippet.getAPICallSite();

        // Whether enqueue or execute, the caller is a Call object 
        // And we need to find the request body through the Call object copy statement client.newCall(request) to do backward data flow analysis (also can sequentially analyze related function calls).
        for(CallSite cs : snippet.callstacks){
            if(cs.callee==null)
                continue;
            if(cs.callee.getDeclaringClass().getName().contains("OkHttpClient")&&cs.callee.getName().equals("newCall")){
                Stmt newCallInvoke = (Stmt) cs.invokeUnit;
                ValueBox requestObj = newCallInvoke.getInvokeExpr().getArgBox(0);
                if(findURLObject_backward(snippet.getLastCaller(),snippet.getAPIinvoke(),requestObj,snippet.callstacks,true))
                    hasURLinRequest = true;
            }
            if(cs.callee.getName().equals("url")){ // for Request.Builder().url(url)
                Stmt setURL = (Stmt) cs.invokeUnit;
                ValueBox urlObj = setURL.getInvokeExpr().getArgBox(0);
                if(findURLObject_backward(snippet.getLastCaller(),snippet.getAPIinvoke(),urlObj,snippet.callstacks,true))
                    hasURLinRequest = true;
            }
            if(cs.callee.getName().equals("post")){
                Stmt postStmt = (Stmt) cs.invokeUnit;
                ValueBox postBody = postStmt.getInvokeExpr().getArgBox(0);
                if(findURLObject_backward(snippet.getLastCaller(),snippet.getAPIinvoke(),postBody,snippet.callstacks,true))
                    hasURLinRequest = true;
            }
            if(cs.callee.getName().toLowerCase().contains("create")){
                Stmt createStmt = (Stmt) cs.invokeUnit;
                if(cs.callee.getParameterCount() == 2) // requestBodyMCE
                {
                    ValueBox bodyValue = createStmt.getInvokeExpr().getArgBox(1);
                    if(findURLObject_backward(snippet.getLastCaller(),snippet.getAPIinvoke(),bodyValue,snippet.callstacks,true))
                        hasURLinRequest = true;
                }
            }
        }

        if(hasURLinRequest){
            if(apiCallSite.callee.getName().equals("execute")){ // Analyze synchronous function calls
                // 定位同步Callback
                this.callBack.add(apiCallSite.callee);
                ValueBox response = null;
                try{
                    response = ((Stmt)apiCallSite.invokeUnit).getDefBoxes().get(0);
                }catch (Exception e){

                }
                if(findURLObject_forward(snippet.getLastCaller(), apiCallSite.invokeUnit, response,0))
                    this.hasURLinResponse = true;
            }else{ //Analyze asynchronous function calls: enqueue
                Type classType = ((Stmt) apiCallSite.invokeUnit).getInvokeExpr().getArgBox(0).getValue().getType();
                if(classType.toString().equals("Callback")){
                    SootClass callbackClass = Scene.v().getSootClass(classType.toString());
                    for(SootMethod sm : callbackClass.getMethods()){
                        if(sm.getName().equals("onResponse")){
                            this.callBack.add(sm);
                            if(findURLObject_forward(sm,null,null,1))
                                this.hasURLinResponse = true;
                        }
                    }
                }
            }
        }

        recordResult(snippet);

    }

}
