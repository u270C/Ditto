package dataflow;

import cfg.CfgFactory;
import javafx.util.Pair;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.ValueBox;
import soot.jimple.*;
import soot.toolkits.graph.BriefUnitGraph;
import util.Log;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

/**
 * @program: Ditto
 * @description: Support the forward dataflow analysis.
 **/
public class ForwardDataFlow extends AbstractDataFlow {

    private static final Logger logger = LoggerFactory.getLogger(ForwardDataFlow.class);

    public static HashMap<String,HashSet<String>> visitedMethod2TaintParamIndex=new HashMap<>();//Record which methods have been accessed as contamination variables
    public static HashMap<Pair<String,String>,HashSet<Point>> methodParamIndexMap2StrawPoint=new HashMap<>();


    public ForwardDataFlow(Analyze analyze) {
        this.analyze = analyze;
    }

    public boolean findFlag=false;

    public void setFindFlag(boolean flag){
        findFlag=flag;
    }

    public boolean getFindFlag(){
        return findFlag;
    }

    @Override
    public boolean caseAnalyze(Unit unit, SootMethod method, List<CallSite> callStack,HashSet<Point> res,ValueBox taintValueBox) {
        return analyze.caseAnalyze(unit, method, callStack,res,taintValueBox);
    }

    @Override
    public boolean returnStatus() {
        return false;
    }

    public void run(SootMethod method, Unit beginUnit, ValueBox beginValueBox, int paramIndex, int depth, List<CallSite> callStack) {
        inter_forward_dataflow(method, beginUnit, beginValueBox, paramIndex, depth, callStack);
    }

    private HashSet<String> taintWrapper=new HashSet<>();

    public void setTaintWrapper(HashSet<String> taintWrapper){
        this.taintWrapper.addAll(taintWrapper);
    }


    public HashSet<String> inter_forward_dataflow(SootMethod method, Unit beginUnit, ValueBox beginValueBox, int paramIndex, int depth, List<CallSite> callStack) {
        // The granularity of the analysis is coarser, and only parameters and return values are analyzed 
        // Store the data for interprocess data flow analysis in methodMap2TaintUnit
        if (depth > MAX_DEPTH) {
            logger.info("exceed the max depth");
            return null;
        }
        if(beginUnit==null&&beginValueBox==null&&method!=null) {
            if (visitedMethod2TaintParamIndex.containsKey(method.getSignature())) {
                if (visitedMethod2TaintParamIndex.get(method.getSignature()).contains(String.valueOf(paramIndex))){
                    Pair<String,String> methodParamTuple=new Pair<>(method.getSignature(),String.valueOf(paramIndex));
                    if(methodParamIndexMap2StrawPoint.containsKey(methodParamTuple)){
                        caseAnalyze(null,null,callStack,methodParamIndexMap2StrawPoint.get(methodParamTuple),null);
                    }
                    return null;
                }else {
                    //If this parameter of the method has not been analyzed, we add the parameter to it
                    visitedMethod2TaintParamIndex.get(method.getSignature()).add(String.valueOf(paramIndex));
                }
            } else {
                //If it is a method that has never been accessed
                HashSet<String> paramSet = new HashSet<>();
                paramSet.add(String.valueOf(paramIndex));
                visitedMethod2TaintParamIndex.put(method.getSignature(),paramSet);
            }
        }

        if (method == null)
            return null;

        if (isMethodCalled(callStack, method))
            return null;

        BriefUnitGraph cfg = CfgFactory.getInstance().getCFG(method);
        if (cfg == null) {
            logger.warn("the cfg of {} is null", method.getSignature());
            return null;
        }
        Event beginEvent;
        HashSet<String> retTaintValue = new HashSet<>();
        if (beginUnit != null && beginValueBox != null) {
            beginEvent = new Event(beginUnit, beginValueBox);
        } else {
            Unit parmaAssignUnit = getParmaAssignUnit(cfg, paramIndex);
            assert parmaAssignUnit != null;
            ValueBox paramValue = parmaAssignUnit.getDefBoxes().get(0);
            beginEvent = new Event(parmaAssignUnit, paramValue);
        }

        EventQueue waitForProcessEvent = new EventQueue();
        waitForProcessEvent.add(beginEvent);

        HashSet<Event> processedEvent = new HashSet<>();

        while (!waitForProcessEvent.isEmpty()) {
            Event e = waitForProcessEvent.poll();
            processedEvent.add(e);
            Unit currentUnit = e.unit;
            ValueBox taintValueBox = e.valueBox;
            if (cfg.getSuccsOf(currentUnit).isEmpty()) {
                if(beginUnit==null) {
                    if (taintValueBox.getValue().toString().startsWith("r0")) {
                        retTaintValue.add("THIS_" + taintValueBox.getValue().toString());
                    }
                    if (currentUnit instanceof ReturnStmt) {
                        ReturnStmt returnStmt = (ReturnStmt) currentUnit;
                        if (!returnStmt.getOp().toString().equals("null") && isValueUsedInUnit(currentUnit, taintValueBox.getValue())) {
                            retTaintValue.add("RET_" + returnStmt.getOp().toString());
                        }
                    }
                }else {
                    CallSite preCallSite = getPreCallSite(callStack);
                    if(preCallSite==null)
                        continue;
                    if(taintValueBox.getValue().toString().startsWith("r0")){
                        InvokeExpr invokeExpr = getInvokeExpr(preCallSite.invokeUnit);
                        if(invokeExpr==null)
                            continue;
                        ValueBox valueBox = invokeExpr.getUseBoxes().get(invokeExpr.getUseBoxes().size() - 1);
                        inter_forward_dataflow(preCallSite.caller,preCallSite.invokeUnit,valueBox,-1,0,copyAndRemoveLast(callStack));
                    }
                    if((preCallSite.invokeUnit instanceof AssignStmt)&&(currentUnit instanceof ReturnStmt)&&isValueUsedInUnit(currentUnit,taintValueBox.getValue())) {
                        DefinitionStmt definitionStmt = (DefinitionStmt) preCallSite.invokeUnit;
                        ValueBox valueBox = definitionStmt.getDefBoxes().get(0);
                        inter_forward_dataflow(preCallSite.caller,preCallSite.invokeUnit,valueBox,-1,0,copyAndRemoveLast(callStack));
                    }
                }
            } else {
                for (Unit succor : cfg.getSuccsOf(currentUnit)) {
                    if (!isValueDefinedInUnit(succor, taintValueBox.getValue())) {
                        Event old_event = new Event(succor, taintValueBox);
                        if (!processedEvent.contains(old_event)&& !waitForProcessEvent.contains(old_event))
                            waitForProcessEvent.add(old_event);
                        if (isValueUsedInUnit(succor, taintValueBox.getValue())) {
                            if(caseAnalyze(succor, method, callStack,null,taintValueBox)) // User-defined analysis interface: for analyze customized interface or sink methods.
                                setFindFlag(true);
                            if (succor instanceof AssignStmt) {
                                AssignStmt assignStmt = (AssignStmt) succor;
                                if (assignStmt.containsFieldRef()) {
                                    Event new_event = new Event(succor, succor.getDefBoxes().get(0));
                                    if (!processedEvent.contains(new_event)&& !waitForProcessEvent.contains(new_event)) {
                                        waitForProcessEvent.add(new_event);
                                    }
                                } else if (assignStmt.containsInvokeExpr()) {
                                    int index = assignStmt.getInvokeExpr().getArgs().indexOf(taintValueBox.getValue());
                                    SootClass declaringClass = assignStmt.getInvokeExpr().getMethod().getDeclaringClass();
                                    if (index != -1) {
                                        if (!isSystemClass(declaringClass)) {
                                            List<CallSite> new_callStack = new ArrayList<>(callStack);
                                            new_callStack.add(new CallSite(method, succor,index));
                                            for(SootMethod calleeMethod:getMethodFromCG(succor)) {
                                                HashSet<String> retRes = inter_forward_dataflow(calleeMethod, null, null, index, depth + 1, new_callStack);
                                                if (retRes != null && retRes.size() != 0) {
                                                    for (String r : retRes) {
                                                        if (r.startsWith("RET")) {
                                                            Event new_event = new Event(succor, succor.getDefBoxes().get(0));
                                                            if (!processedEvent.contains(new_event)&& !waitForProcessEvent.contains(new_event))
                                                                waitForProcessEvent.add(new_event);
                                                        } else {
                                                            InvokeExpr invokeExpr = assignStmt.getInvokeExpr();
                                                            if (!(invokeExpr instanceof StaticInvokeExpr)) {
                                                                ValueBox thisValueBox = invokeExpr.getUseBoxes().get(invokeExpr.getUseBoxes().size() - 1);
                                                                Event event = new Event(succor, thisValueBox);
                                                                if (!processedEvent.contains(event)&&!waitForProcessEvent.contains(event)) {
                                                                    waitForProcessEvent.add(event);
                                                                }
                                                            }
                                                        }

                                                    }
                                                }
                                            }
                                        } else {
                                            //If a contaminated variable is introduced into the system method, we no longer do the interprocedural analysis and simply assume that the return value is contaminated
                                            Event new_event = new Event(succor, succor.getDefBoxes().get(0));
                                            if (!processedEvent.contains(new_event)&&!waitForProcessEvent.contains(new_event))
                                                waitForProcessEvent.add(new_event);
                                            InvokeExpr invokeExpr = assignStmt.getInvokeExpr();
                                            if (!(invokeExpr instanceof StaticInvokeExpr)) {
                                                ValueBox ref = assignStmt.getUseBoxes().get(assignStmt.getUseBoxes().size() - 1);
                                                new_event = new Event(succor, ref);
                                                if (!processedEvent.contains(new_event)&&!waitForProcessEvent.contains(new_event))
                                                    waitForProcessEvent.add(new_event);
                                            }
                                        }
                                    } else {
                                        //r.a(xxx,xxx),r is tanited
                                        if (isSystemClass(declaringClass)) {
                                            Event new_event = new Event(succor, succor.getDefBoxes().get(0));
                                            if (!processedEvent.contains(new_event)&&!waitForProcessEvent.contains(new_event))
                                                waitForProcessEvent.add(new_event);
                                        } else {
                                            Event new_event = new Event(succor, succor.getDefBoxes().get(0));
                                            if (!processedEvent.contains(new_event)&&!waitForProcessEvent.contains(new_event))
                                                waitForProcessEvent.add(new_event);
                                        }

                                    }
                                } else if (assignStmt.containsArrayRef()) {//for a=b[i]
                                    Event new_event = new Event(succor, succor.getDefBoxes().get(0));
                                    if (!processedEvent.contains(new_event)&&!waitForProcessEvent.contains(new_event))
                                        waitForProcessEvent.add(new_event);
                                } else {
                                    //for a=b
                                    Event new_event = new Event(succor, succor.getDefBoxes().get(0));
                                    if (!processedEvent.contains(new_event)&& !waitForProcessEvent.contains(new_event))
                                        waitForProcessEvent.add(new_event);
                                }
                            } else if (succor instanceof InvokeStmt) {
                                //for void a.()
                                InvokeStmt invokeStmt = (InvokeStmt) succor;
                                int index = invokeStmt.getInvokeExpr().getArgs().indexOf(taintValueBox.getValue());
                                if (index != -1) {
                                    SootClass declaringClass = invokeStmt.getInvokeExpr().getMethod().getDeclaringClass();
                                    if (!isSystemClass(declaringClass)) {
                                        InvokeExpr expr = invokeStmt.getInvokeExpr();
                                        String methodName=expr.getMethod().getName();
                                        String className=declaringClass.getName();

                                        if(methodName.equals("<init>")){
                                            InvokeExpr invokeExpr = invokeStmt.getInvokeExpr();
                                            int size = invokeExpr.getUseBoxes().size();
                                            ValueBox valueBox = invokeExpr.getUseBoxes().get(size - 1);
                                            Event event = new Event(succor, valueBox);
                                            if (!processedEvent.contains(event)&&!waitForProcessEvent.contains(event)) {
                                                waitForProcessEvent.add(event);
                                            }
                                        }
                                        if(className.startsWith("android")||className.startsWith("com.android")){
                                            if(methodName.contains("put")||methodName.contains("add")||methodName.contains("insert")){
                                                InvokeExpr invokeExpr = invokeStmt.getInvokeExpr();
                                                int size = invokeExpr.getUseBoxes().size();
                                                ValueBox valueBox = invokeExpr.getUseBoxes().get(size - 1);
                                                Event event = new Event(succor, valueBox);
                                                if (!processedEvent.contains(event)&&!waitForProcessEvent.contains(event)) {
                                                    waitForProcessEvent.add(event);
                                                }
                                            }
                                        }
                                        List<CallSite> new_callStack = new ArrayList<>(callStack);
                                        new_callStack.add(new CallSite(method, succor,index));
                                        for(SootMethod calleeMethod:getMethodFromCG(succor)) {
                                            HashSet<String> ret = inter_forward_dataflow(calleeMethod, null, null, index, depth + 1, new_callStack);
                                            if (ret != null && ret.size() != 0) {
                                                for (String r : ret) {
                                                    if (r.startsWith("THIS")) {
                                                        if (!(invokeStmt.getInvokeExpr() instanceof StaticInvokeExpr)) {
                                                            InvokeExpr invokeExpr = invokeStmt.getInvokeExpr();
                                                            ValueBox thisValueBox = invokeExpr.getUseBoxes().get(invokeExpr.getUseBoxes().size() - 1);
                                                            Event event = new Event(succor, thisValueBox);
                                                            if (!processedEvent.contains(event)&&!waitForProcessEvent.contains(event)) {
                                                                waitForProcessEvent.add(event);
                                                                break;
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }else {
                                        String signature = invokeStmt.getInvokeExpr().getMethod().getSignature();
                                        String methodName = invokeStmt.getInvokeExpr().getMethod().getName();
                                        if(methodName.equals("<init>")){
                                            InvokeExpr invokeExpr = invokeStmt.getInvokeExpr();
                                            int size = invokeExpr.getUseBoxes().size();
                                            ValueBox valueBox = invokeExpr.getUseBoxes().get(size - 1);
                                            Event event = new Event(succor, valueBox);
                                            if (!processedEvent.contains(event)&&!waitForProcessEvent.contains(event)) {
                                                waitForProcessEvent.add(event);
                                            }
                                        }
                                        if(signature.equals("<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>")){
                                            InvokeExpr invokeExpr = invokeStmt.getInvokeExpr();
                                            int size = invokeExpr.getUseBoxes().size();
                                            ValueBox valueBox = invokeExpr.getUseBoxes().get(size - 1);
                                            Event event = new Event(succor, valueBox);
                                            if (!processedEvent.contains(event)&&!waitForProcessEvent.contains(event)) {
                                                waitForProcessEvent.add(event);
                                            }
                                        }
                                    }
                                } else {
                                    String signature = invokeStmt.getInvokeExpr().getMethod().getSignature();
                                    if(taintWrapper.contains(signature)){
                                        InvokeExpr invokeExpr = invokeStmt.getInvokeExpr();
                                        ValueBox valueBox = invokeExpr.getArgBox(0);
                                        Event event = new Event(succor, valueBox);
                                        if (!processedEvent.contains(event)&&!waitForProcessEvent.contains(event)) {
                                            waitForProcessEvent.add(event);
                                        }
                                    }
                                }
                            }
                        }
                    }

                }

            }
        }
        return retTaintValue;
    }

    public static void addCheckedInfo2MethodParam2StrawPoint(List<CallSite> callStack,HashSet<Point> res){
        if(callStack.size()==0||res==null)
            return;
        for(CallSite callSite:callStack){
            int paramIndex = callSite.paramIndex;
            if(paramIndex==-1)
                continue;
            Pair<String,String> methodParamPair=new Pair<>(callSite.caller.getSignature(),String.valueOf(paramIndex));
            if(!methodParamIndexMap2StrawPoint.containsKey(methodParamPair))
                methodParamIndexMap2StrawPoint.put(methodParamPair,new HashSet<>());
            methodParamIndexMap2StrawPoint.get(methodParamPair).addAll(res);
        }
    }

    public CallSite getPreCallSite(List<CallSite> callStack) {
        if (callStack.size() == 0)
            return null;
        return callStack.get(callStack.size() - 1);

    }

    public List<CallSite> copyAndRemoveLast(List<CallSite> callStack) {
        List<CallSite> new_callStack = new ArrayList<>(callStack);
        new_callStack.remove(callStack.size() - 1);
        return new_callStack;
    }

    public List<CallSite> copyAndAddLast(List<CallSite> callStack, CallSite callSite) {
        List<CallSite> new_callStack = new ArrayList<>(callStack);
        new_callStack.add(callSite);
        return new_callStack;
    }



}
