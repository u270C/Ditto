package dataflow;

import constant.StrawPointsDefinition;
import javafx.scene.Scene;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.*;
import soot.jimple.*;
import soot.jimple.internal.VariableBox;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.jimple.toolkits.callgraph.ReachableMethods;
import soot.jimple.toolkits.ide.icfg.JimpleBasedInterproceduralCFG;
import soot.tagkit.AttributeValueException;
import soot.tagkit.Tag;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.DirectedGraph;
import soot.toolkits.graph.MHGPostDominatorsFinder;
import soot.util.HashMultiMap;
import soot.util.MultiMap;
import soot.util.queue.QueueReader;

import java.util.*;

/**
 * @program: Ditto
 * @description: Used to detect the use of sensitive data in applications. The main work is data flow analysis based on ICFG.
 **/
public class DataFlowEngine {

    public static final Logger logger = LoggerFactory.getLogger(DataFlowEngine.class);

    public static JimpleBasedInterproceduralCFG icfg = null;

    public static TaintWrapper taintWrapper = new TaintWrapper();

    public static HashMap<Integer, HashSet<ValueBox>> inputMapOutCache = new HashMap<>();

    public MultiMap<SootField, Unit> staticField2MapLoadSite = new HashMultiMap<>();
    
    public MultiMap<SootField,Unit> singleTonFieldMap2LoadSite=new HashMultiMap<>();

    //The maximum depth analyzed downward from the sink point, the greater the depth, the lower the accuracy
    protected int maxDepth = 10;


    public RuleChecker checker = null;//Rule checker

    public void setChecker(RuleChecker checker) {
        this.checker = checker;
    }

    //Implicit flow mode, implicit flow is not handled by default, because implicit flow back causes very large false positives and overhead
    private boolean implicitMode=false;

    public void setImplicitMode(boolean implicitMode){
        this.implicitMode=implicitMode;
    }

    //Contaminated fields that have been globally tracked
    private HashSet<SootField> tracedGlobalTaintValue=new HashSet<>();


    private long start_time;

    
    private double time_out=300;

    public void setTimeOut(double time_out){
        this.time_out=time_out;
    }

    //Sets the time_out flag bit, which is set to true if the time expires

    private boolean is_time_out(){
        if((System.nanoTime()-start_time)/1E9>time_out)
            return true;
        return false;
    }

    private boolean isTrackGlobalTaintValue=false;

    public void setTracedGlobalTaintValue(boolean isTrackGlobalTaintValue){
        this.isTrackGlobalTaintValue=isTrackGlobalTaintValue;
    }

    public final Tag retTag = new Tag() {
        @Override
        public String getName() {
            return "RetValue";
        }

        @Override
        public byte[] getValue() throws AttributeValueException {
            return new byte[0];
        }
    };

    public final Tag paramTag = new Tag() {
        @Override
        public String getName() {
            return "Param";
        }

        @Override
        public byte[] getValue() throws AttributeValueException {
            return new byte[0];
        }
    };

    public final Tag staticFiledTag = new Tag() {
        @Override
        public String getName() {
            return "StaticField";
        }

        @Override
        public byte[] getValue() throws AttributeValueException {
            return new byte[0];
        }
    };

    public final Tag thisTag = new Tag() {
        @Override
        public String getName() {
            return "This";
        }

        @Override
        public byte[] getValue() throws AttributeValueException {
            return new byte[0];
        }
    };

    public final Tag instanceFieldTag = new Tag() {
        @Override
        public String getName() {
            return "InstanceField";
        }

        @Override
        public byte[] getValue() throws AttributeValueException {
            return new byte[0];
        }
    };

    static class MethodTaintOutPut {
        /*

         */
        public HashSet<ValueBox> taintValueBox;
        public SootMethod taintMethod;

        public MethodTaintOutPut(HashSet<ValueBox> taintValueBox, SootMethod taintMethod) {
            this.taintValueBox = taintValueBox;
            this.taintMethod = taintMethod;
        }

        @Override
        public boolean equals(Object obj) {
            if(!(obj instanceof MethodTaintOutPut))
                return false;
            MethodTaintOutPut taint = (MethodTaintOutPut) obj;
            if(!taint.taintMethod.equals(this.taintMethod))
                return false;
            return super.equals(obj);
        }

        @Override
        public int hashCode() {
            return Objects.hash(taintMethod, taintValueBox);
        }
    }

    public void setMaxDepth(int depth){
        this.maxDepth=depth;
    }
    /*
    Constructor method, parameter ICFG, the user must provide an interprocedural control flow diagram of the program
     */
    public DataFlowEngine(JimpleBasedInterproceduralCFG icfg) {
        this.icfg = icfg;
        preAnalysis();
        start_time=System.nanoTime();
    }

    /*
    Specifies a statement within a method for data tracing
     */
    public void runFlowAnalysis(SootMethod method, Unit sinkUnit,String accessPath) {
        if(!(sinkUnit instanceof AssignStmt)&&!(sinkUnit instanceof IdentityStmt)) {
            logger.info("{} is not an assign unit!",sinkUnit);
            return;
        }
        ValueBox headBox = sinkUnit.getDefBoxes().get(0);
        headBox.addTag(new AccessPathTag());
        if(accessPath!=null&&!accessPath.isEmpty()){
            AccessPathTag accessPathTag = new AccessPathTag();
            accessPathTag.appendAccessPath(accessPath);
            headBox.addTag(accessPathTag);
            headBox.addTag(instanceFieldTag);
        }else {
            headBox.addTag(new AccessPathTag());
        }
        HashSet<ValueBox> outPut = forwardDataFlow(method, null, sinkUnit, headBox, -1, 0);
        //Records processed calls
        if(outPut==null)
            return;
        HashSet<Unit> visitedInvoke=new HashSet<>();
        MethodTaintOutPut methodTaintOutPut = new MethodTaintOutPut(outPut, method);
        Queue<MethodTaintOutPut> queue = new LinkedList<>();
        queue.add(methodTaintOutPut);
        while (!queue.isEmpty()) {
            MethodTaintOutPut poll = queue.poll();
            SootMethod callee = poll.taintMethod;
            HashSet<ValueBox> taintValueBox = poll.taintValueBox;
            for (Unit callSiteStmt : icfg.getCallersOf(callee)) {
                if(visitedInvoke.contains(callSiteStmt))
                    continue;
                visitedInvoke.add(callSiteStmt);
                SootMethod caller = icfg.getMethodOf(callSiteStmt);
                InvokeExpr invokeExpr = getInvokeExpr(callSiteStmt);
                if (invokeExpr == null)
                    continue;
                for (ValueBox valueBox : taintValueBox) {
                    //We need to analyze based on the type of result returned
                    if (valueBox.getTag("Param") != null) {
                        //If it is a parameter return we should continue to propagate that parameter
                        int index = callee.retrieveActiveBody().getParameterLocals().indexOf((Local) valueBox.getValue());
                        //We should get the arguments for this parameter
                        if(index==-1)
                            continue;
                        Value arg = invokeExpr.getArg(index);
                        if(arg instanceof Constant)
                            continue;
                        VariableBox variableBox = new VariableBox(arg);
                        variableBox.addTag(new AccessPathTag(valueBox.getTag("AccessPath")));
                        //For parameters, you should actually do alias analysis, but we won't do it here
                        HashSet<ValueBox> valueBoxes = forwardDataFlow(caller, null, callSiteStmt, variableBox, -1, 0);
                        if (valueBoxes!=null&&valueBoxes.size() != 0) {
                            MethodTaintOutPut res = new MethodTaintOutPut(valueBoxes, caller);
                            queue.add(res);
                        }
                    } else if (valueBox.getTag("RetValue") != null) {
                        if (callSiteStmt instanceof AssignStmt) {
                            AssignStmt assignStmt = (AssignStmt) callSiteStmt;
                            VariableBox variableBox = new VariableBox(assignStmt.getDefBoxes().get(0).getValue());
                            variableBox.addTag(new AccessPathTag(valueBox.getTag("AccessPath")));
                            HashSet<ValueBox> valueBoxes = forwardDataFlow(caller, null, callSiteStmt, variableBox, -1, 0);

                            if (valueBoxes!=null&&valueBoxes.size() != 0) {
                                MethodTaintOutPut res = new MethodTaintOutPut(valueBoxes, caller);
                                queue.add(res);
                            }
                        }

                    } else if (valueBox.getTag("This") != null) {
                        //The example should continue to be disseminated
                        ValueBox baseValue = invokeExpr.getUseBoxes().get(invokeExpr.getUseBoxes().size() - 1);
                        VariableBox variableBox = new VariableBox(baseValue.getValue());
                        variableBox.addTag(new AccessPathTag());
                        HashSet<ValueBox> valueBoxes = forwardDataFlow(caller, null, callSiteStmt, variableBox, -1, 0);
                        if (valueBoxes!=null&&valueBoxes.size() != 0) {
                            MethodTaintOutPut res = new MethodTaintOutPut(valueBoxes, caller);
                            queue.add(res);
                        }
                    } else if (valueBox.getTag("InstanceField") != null&&!(invokeExpr instanceof StaticInvokeExpr)) {
                        //If the instance field is contaminated, we should do alias analysis
                        Value baseBox = getBaseBox(invokeExpr);
                        VariableBox variableBox = new VariableBox(baseBox);
                        variableBox.addTag(valueBox.getTag("AccessPath"));
                        HashSet<ValueBox> valueBoxes = onDemandBackWardAliasAnalyze(caller, variableBox, callSiteStmt);
                        variableBox.addTag(instanceFieldTag);
                        valueBoxes.add(variableBox);
                        for (ValueBox alias : valueBoxes) {
                            HashSet<ValueBox> valueBoxes1 = forwardDataFlow(caller, null, callSiteStmt, alias, -1, 0);
                            if (valueBoxes1!=null&&valueBoxes1.size() != 0) {
                                MethodTaintOutPut res = new MethodTaintOutPut(valueBoxes1, caller);
                                queue.add(res);
                            }

                        }
                    }

                }
            }
        }
    }

    //Gets the call expression in the statement
    public InvokeExpr getInvokeExpr(Unit unit) {
        if (unit instanceof AssignStmt) {
            AssignStmt assignStmt = (AssignStmt) unit;
            if (assignStmt.containsInvokeExpr())
                return assignStmt.getInvokeExpr();
        } else if (unit instanceof InvokeStmt) {
            InvokeStmt invokeStmt = (InvokeStmt) unit;
            return invokeStmt.getInvokeExpr();
        }
        return null;
    }

    /*
    Function: This method performs inter-process data flow analysis. In addition to a problem of accuracy, its data flow analysis can only trace the method existing in the source and related calls, and does not have the ability to trace the caller of the method where the source is located 
    Note: Because this is done recursively, this part of the code is context-sensitive, thus reducing asynchronous false positives 
    This section can also be written in a non-recursive way for optimization 
    Input: Method to analyze, contamination variable, parameter number, call depth 
    The contamination variable is in the form of ValueBox, which has some auxiliary tag, which we must here is AccessPath, the value of valuebox is the variable name, and the access path is its specific value on the heap 
    For example, a pollution variable whose value is r10 has an access path of x.y. Then its true pollution value is r10.x.y 
    A valuebox whose access path is empty indicates that this is the object to which the reference refers is contaminated 
    For static variables, value is the field itself
     */
    public HashSet<ValueBox> forwardDataFlow(SootMethod method, ValueBox valueBox, Unit taintUnit, ValueBox taintValueBox, int paramIndex, int depth) {
        /*
        ===============================================================================================
        ========================================Data Flow Analysis Engine============================================
        ===============================================================================================
       Flow sensitive, context sensitive, field sensitive
         */

        if (depth > maxDepth) {
            return null;
        }
        if(is_time_out()){
            logger.info("Analyze time out!");
            return null;
        }

        Body body;
        if(method.isPhantom()||method.isNative()||!method.isConcrete()){
            logger.info("No body for {}",method.getSignature());



            if(taintUnit!=null&&taintValueBox!=null){
                return null;
            }
            HashSet<ValueBox> ans=new HashSet<>();

            if(paramIndex==-1){
                //If the field is static
                valueBox.addTag(staticFiledTag);
            }else if(paramIndex==-2){
                //If it is an instance field
                valueBox.addTag(instanceFieldTag);
            }else if(paramIndex==-3){
                //If object itself
                valueBox.addTag(thisTag);
            }else if(paramIndex>=0){
                //If parameter
                valueBox.addTag(paramTag);
            }
            ans.add(valueBox);
            return ans;
        }
        body = method.retrieveActiveBody();

        BriefUnitGraph graph = new BriefUnitGraph(body);
        Unit unit = null;

        if (taintUnit != null && taintValueBox != null) {
            valueBox = taintValueBox;
            unit = taintUnit;
        } else if (paramIndex >= 0) {
            unit = getArgumentsAssignment(method, paramIndex);
            if (unit == null)
                return null;
            ValueBox paramBox = unit.getDefBoxes().get(0);
            paramBox.addTag(new AccessPathTag(valueBox.getTag("AccessPath")));
            paramBox.addTag(paramTag);
            valueBox = paramBox;
        } else if (paramIndex == -1) {
            //The value is -1, indicating a static field
            for (Unit head : graph.getHeads()) {
                if (!head.toString().equals("@caughtexception")) {
                    unit = head;
                    break;
                }
            }
        } else if (paramIndex == -2) {
            //The value is -2, indicating the instance field
            Value thisLocal =(Value) method.retrieveActiveBody().getThisLocal();
            AccessPathTag accessPath = new AccessPathTag(valueBox.getTag("AccessPath"));
            VariableBox variableBox = new VariableBox(thisLocal);
            variableBox.addTag(accessPath);
            variableBox.addTag(instanceFieldTag);
            valueBox = variableBox;
            unit = method.retrieveActiveBody().getThisUnit();
        } else if (paramIndex == -3) {
            // represents the object itself, and we go directly to the object itself
            Unit thisUnit = method.retrieveActiveBody().getThisUnit();
            Local thisLocal = method.retrieveActiveBody().getThisLocal();
            unit=thisUnit;
            valueBox=new VariableBox(thisLocal);
            valueBox.addTag(thisTag);
            valueBox.addTag(new AccessPathTag());
        }

        String key = method.getSignature() + valueBox.getValue().toString() + ((AccessPathTag) valueBox.getTag("AccessPath")).getFieldChain();
        int mark = key.hashCode();
        if (inputMapOutCache.containsKey(mark))
            return inputMapOutCache.get(mark);

        EventQueue workList = new EventQueue();
        workList.add(new Event(unit, valueBox));
        HashSet<Event> processedEvent = new HashSet<>();
        HashSet<ValueBox> res = new HashSet<>();
       
        HashSet<Unit> checkedIfSet=new HashSet<>();

        while (!workList.isEmpty()) {
            if(is_time_out()){
                logger.info("Analyze time out!");
                return null;
            }
            Event poll = workList.poll();
            processedEvent.add(poll);
            Unit curUnit = poll.unit;
            ValueBox curValueBox = poll.valueBox;
            
            for (Unit checkedUnit : graph.getSuccsOf(curUnit)) {
                if (!isValueDefinedInUnit(checkedUnit, curValueBox.getValue())) {
                    //1. Handle the return point first 
                    // If the return value of the current statement is contaminated, such as return r, and r is the contaminated variable, we should record its information and return the lvalue of the call point 
                    // If it is a global variable, we should return to the call point 
                    // If it is a field of this object, we should return it to the call point 
                    // If it is a local variable, our propagation should end 
                    // If it is a parameter, we should also return the call point
                    if ((checkedUnit instanceof ReturnStmt) || (checkedUnit instanceof RetStmt) || (checkedUnit instanceof ReturnVoidStmt)) {
                        Value value = curValueBox.getValue();
                        if(!(value instanceof StaticFieldRef)&&!method.isStatic()){
                            AccessPathTag accessPath = (AccessPathTag) curValueBox.getTag("AccessPath");
                            Local thisLocal = method.retrieveActiveBody().getThisLocal();
                            if(thisLocal.equals(value)&&accessPath.getFieldLength()>0){
                                curValueBox.addTag(instanceFieldTag);
                            }else if(thisLocal.equals(value)){
                                curValueBox.addTag(thisTag);
                            }
                        }else {
                            curValueBox.addTag(staticFiledTag);
                        }
                        if (isValueUsedInUnit(checkedUnit, curValueBox.getValue())) {
                            curValueBox.addTag(retTag);
                            res.add(curValueBox);
                        } else if (curValueBox.getTag("InstanceField") != null&&!method.isStatic()) {
                            Local thisLocal = method.retrieveActiveBody().getThisLocal();
                            String baseValue = curValueBox.getValue().getType().toString();
                            String className = method.getDeclaringClass().getName();
                            if (baseValue.equals(thisLocal.toString()) || className.equals(baseValue)) {
                                res.add(curValueBox);
                            }
                        } else if (curValueBox.getTag("StaticField") != null) {
                            res.add(curValueBox);
                        } else if (curValueBox.getTag("Param") != null) {
                            res.add(curValueBox);
                        } else if (curValueBox.getTag("This") != null || (!method.isStatic()&&curValueBox.getValue().equals(method.retrieveActiveBody().getThisLocal()))) {
                            res.add(curValueBox);
                        } else if (curValueBox.getValue() instanceof Local && method.retrieveActiveBody().getParameterLocals().contains((Local) curValueBox.getValue())) {
                            curValueBox.addTag(paramTag);
                            res.add(curValueBox);
                        }
                    }
                    else if ((checkedUnit instanceof InvokeStmt) || ((checkedUnit instanceof AssignStmt) && ((AssignStmt) checkedUnit).containsInvokeExpr())) {
                        //2, then handle the call point situation 
                        // There are four cases passed in: global variables, parameters, instance fields, and the object itself 
                        // Determine whether it is a sink
                        checker.isSink(checkedUnit,curValueBox);

                        if (isValueUsedInUnit(checkedUnit, curValueBox.getValue()) || curValueBox.getValue() instanceof StaticFieldRef) {
                            InvokeExpr invokeExpr ;
                            if (checkedUnit instanceof InvokeStmt) {
                                InvokeStmt invokeStmt = (InvokeStmt) checkedUnit;
                                invokeExpr = invokeStmt.getInvokeExpr();
                            } else {
                                AssignStmt assignStmt = (AssignStmt) checkedUnit;
                                invokeExpr = assignStmt.getInvokeExpr();
                            }

                            SootMethod callee = invokeExpr.getMethod();

                            if (callee.isNative()) {
                                Event event = new Event(checkedUnit, curValueBox);
                                if (!processedEvent.contains(event) && !workList.contains(event))
                                    workList.add(event);
                            }
                            else if (isSystemClass(callee.getDeclaringClass().getName())) {
                                if (!invokeExpr.getArgs().contains(curValueBox.getValue())) {
                                    Event event = new Event(checkedUnit, curValueBox);
                                    if (!processedEvent.contains(event) && !workList.contains(event))
                                        workList.add(event);
                                }
                                CallGraph callGraph = Scene.v().getCallGraph();
                                Iterator<Edge> edgeIterator = callGraph.edgesOutOf(checkedUnit);
                                boolean flag = false;
                                while (edgeIterator.hasNext()) {
                                    Edge edge = edgeIterator.next();
                                    Kind kind = edge.kind();
                                    if (kind.isFake() || kind.toString().equals("CALLBACK")||kind.toString().equals("SYSTEM_CALL")) {
                                        flag = true;
                                        SootMethod calledMethod = edge.tgt();
                                        if (kind.isFake()) {
                                            if (kind.isThread()) {
                                                if (curValueBox.getValue() instanceof StaticFieldRef) {
                                                    forwardDataFlow(calledMethod, curValueBox, null, null, -1, depth + 1);
                                                } else if (isValueUsedInUnit(checkedUnit, curValueBox.getValue())) {
                                                    AccessPathTag accessPath = (AccessPathTag) curValueBox.getTag("AccessPath");
                                                    if (accessPath.getFieldLength() == 0) {
                                                        forwardDataFlow(calledMethod, curValueBox, null, null, -3, depth + 1);
                                                    } else {
                                                        forwardDataFlow(calledMethod, curValueBox, null, null, -2, depth + 1);
                                                    }
                                                } else {
                                                    Event event = new Event(checkedUnit, curValueBox);
                                                    if (!processedEvent.contains(event) && !workList.contains(event))
                                                        workList.add(event);
                                                }
                                            } else if (kind.isExecutor()) {
                                                if (curValueBox.getValue() instanceof StaticFieldRef) {
                                                    forwardDataFlow(calledMethod, curValueBox, null, null, -1, depth + 1);
                                                } else if (invokeExpr.getArgs().contains(curValueBox.getValue())) {
                                                    forwardDataFlow(calledMethod, curValueBox, null, null, -2, depth + 1);

                                                } else {
                                                    Event event = new Event(checkedUnit, curValueBox);
                                                    if (!processedEvent.contains(event) && !workList.contains(event))
                                                        workList.add(event);
                                                }
                                            } else if (kind.isAsyncTask()) {
                                                if (curValueBox.getValue() instanceof StaticFieldRef) {
                                                    forwardDataFlow(calledMethod, curValueBox, null, null, -1, depth + 1);
                                                } else if (invokeExpr.getArgs().contains(curValueBox.getValue())) {
                                                    forwardDataFlow(calledMethod, curValueBox, null, null, invokeExpr.getArgs().indexOf(curValueBox.getValue()), depth + 1);
                                                } else if (!(invokeExpr instanceof StaticInvokeExpr)) {
                                                    Value baseBox = getBaseBox(invokeExpr);
                                                    if (baseBox.equals(curValueBox.getValue())) {
                                                        AccessPathTag accessPath = (AccessPathTag) curValueBox.getTag("AccessPath");
                                                        if (accessPath.getFieldLength() == 0) {
                                                            forwardDataFlow(calledMethod, curValueBox, null, null, -3, depth + 1);
                                                        } else {
                                                            forwardDataFlow(calledMethod, curValueBox, null, null, -2, depth + 1);
                                                        }
                                                    }
                                                }

                                            } else if (kind == Kind.HANDLER) {
                                                //todo
                                            }
                                        } else if (kind.toString().equals("CALLBACK")) {
                                            if (isValueUsedInUnit(checkedUnit, curValueBox.getValue())) {
                                                forwardDataFlow(calledMethod, curValueBox, null, null, 0, depth + 1);
                                            } else if (curValueBox.getValue() instanceof StaticFieldRef) {
                                                forwardDataFlow(calledMethod, curValueBox, null, null, -1, depth + 1);
                                            }
                                        }else if(kind.toString().equals("SYSTEM_CALL")){
                                            if(calledMethod.getName().equals("onDraw")) {
                                                if (isValueUsedInUnit(checkedUnit, curValueBox.getValue())) {
                                                    forwardDataFlow(calledMethod, curValueBox, null, null, -2, depth + 1);
                                                } else if (curValueBox.getValue() instanceof StaticFieldRef) {
                                                    forwardDataFlow(calledMethod, curValueBox, null, null, -1, depth + 1);
                                                }
                                            }
                                        }

                                    }
                                }
                                if (flag)
                                    continue;
                                Value baseBox = getBaseBox(invokeExpr);
                                boolean taintedInstance = false;
                                if (baseBox != null) {
                                    taintedInstance = baseBox.equals(curValueBox.getValue());
                                }
                                int taintedParamIndex = invokeExpr.getArgs().indexOf(curValueBox.getValue());
                                if (taintWrapper.isInInTaintWrapper(callee.getSignature())) {
                                    boolean instance_flag = taintWrapper.canAffectInstance(callee.getSignature(), taintedParamIndex);
                                    if (instance_flag) {
                                        ValueBox instanceBox = invokeExpr.getUseBoxes().get(invokeExpr.getUseBoxes().size() - 1);
                                        HashSet<ValueBox> valueBoxes = onDemandBackWardAliasAnalyze(method, instanceBox, checkedUnit);
                                        instanceBox.addTag(new AccessPathTag());
                                        valueBoxes.add(instanceBox);
                                        for (ValueBox alias : valueBoxes) {
                                            Value value = alias.getValue();
                                            if (value instanceof InstanceFieldRef) {
                                                InstanceFieldRef fieldRef = (InstanceFieldRef) alias;
                                                VariableBox variableBox1 = new VariableBox(fieldRef.getBase());
                                                AccessPathTag accessPath1 = new AccessPathTag(alias.getTag("AccessPath"));
                                                accessPath1.appendAccessPath(fieldRef.getField().getName());
                                                variableBox1.addTag(accessPath1);
                                                alias = variableBox1;
                                                alias.addTag(instanceFieldTag);
                                            } else if (value instanceof StaticFieldRef) {
                                                alias.addTag(staticFiledTag);
                                            }
                                            Event event = new Event(checkedUnit, alias);
                                            if (!processedEvent.contains(event) && !workList.contains(event))
                                                workList.add(event);
                                        }
                                    }
                                    boolean retValue_flag = taintWrapper.canAffectRetValue(callee.getSignature(), taintedInstance, taintedParamIndex);
                                    if (retValue_flag) {
                                        if (checkedUnit instanceof AssignStmt) {
                                            ValueBox retBox = checkedUnit.getDefBoxes().get(0);
                                            retBox.addTag(new AccessPathTag());
                                            Event retEvent = new Event(checkedUnit, retBox);
                                            if (!processedEvent.contains(retEvent) && !workList.contains(retEvent))
                                                workList.add(retEvent);
                                        }
                                    }
                                    int affectedParamIndex = taintWrapper.getAffectedParamIndex(callee.getSignature(), taintedInstance, taintedParamIndex);
                                    if (affectedParamIndex != -1) {
                                        ValueBox argBox = invokeExpr.getArgBox(affectedParamIndex);
                                        argBox.addTag(new AccessPathTag());
                                        Event argEvent = new Event(checkedUnit, argBox);
                                        if (!processedEvent.contains(argEvent) && !workList.contains(argEvent))
                                            workList.add(argEvent);
                                    }

                                } else {
                                    if (checkedUnit instanceof AssignStmt) {

                                        ValueBox retBox = checkedUnit.getDefBoxes().get(0);
                                        retBox.addTag(new AccessPathTag());
                                        Event retEvent = new Event(checkedUnit, retBox);
                                        if (!processedEvent.contains(retEvent) && !workList.contains(retEvent))
                                            workList.add(retEvent);
                                    }
                                    if (!(invokeExpr instanceof StaticInvokeExpr)) {
                                        Value base = getBaseBox(invokeExpr);
                                        VariableBox instanceBox = new VariableBox(base);
                                        if (isMethodCanAffectHeap(invokeExpr.getMethod().getName()) && invokeExpr.getArgs().contains(curValueBox.getValue())) {
                                            AccessPathTag accessPathTag = new AccessPathTag();
                                            instanceBox.addTag(accessPathTag);
                                            HashSet<ValueBox> valueBoxes = onDemandBackWardAliasAnalyze(method, instanceBox, checkedUnit);
                                            valueBoxes.add(instanceBox);

                                            for (ValueBox alias : valueBoxes) {
                                                Event event = new Event(checkedUnit, alias);
                                                if (!processedEvent.contains(event) && !workList.contains(event)) {
                                                    workList.add(event);
                                                }
                                            }
                                        } else {
                                                instanceBox.addTag(new AccessPathTag());
                                                Event event = new Event(checkedUnit, instanceBox);
                                                if (!processedEvent.contains(event) && !workList.contains(event))
                                                    workList.add(event);
                                        }
                                    }
                                    Event event = new Event(checkedUnit, curValueBox);
                                    if (!processedEvent.contains(event) && !workList.contains(event))
                                        workList.add(event);
                                }
                            } else {
                                CallGraph callGraph = Scene.v().getCallGraph();
                                Iterator<Edge> edgeIterator = callGraph.edgesOutOf(checkedUnit);
                                while (edgeIterator.hasNext()) {
                                    Edge next = edgeIterator.next();
                                    Kind kind = next.kind();
                                    SootMethod calledMethod = next.getTgt().method();
                                    if(calledMethod.isPhantom())
                                        continue;
                                    if (isSystemClass(calledMethod.getDeclaringClass().getName())) {
                                        Event event = new Event(checkedUnit, curValueBox);
                                        if (!processedEvent.contains(event) && !workList.contains(event))
                                            workList.add(event);
                                        continue;
                                    }
                                    HashSet<ValueBox> resultFromCallee = new HashSet<>();
                                    if (kind.isFake()) {
                                        if (kind.isThread()) {
                                            if (curValueBox.getValue() instanceof StaticFieldRef) {
                                                resultFromCallee = forwardDataFlow(calledMethod, curValueBox, null, null, -1, depth + 1);
                                            } else if (isValueUsedInUnit(checkedUnit, curValueBox.getValue())) {
                                                AccessPathTag accessPath = (AccessPathTag) curValueBox.getTag("AccessPath");
                                                if (accessPath.getFieldLength() == 0) {
                                                    resultFromCallee = forwardDataFlow(calledMethod, curValueBox, null, null, -3, depth + 1);
                                                } else {
                                                    resultFromCallee = forwardDataFlow(calledMethod, curValueBox, null, null, -2, depth + 1);
                                                }
                                            } else {
                                                Event event = new Event(checkedUnit, curValueBox);
                                                if (!processedEvent.contains(event) && !workList.contains(event))
                                                    workList.add(event);
                                            }
                                        } else if (kind.isExecutor()) {
                                            if (curValueBox.getValue() instanceof StaticFieldRef) {
                                                resultFromCallee = forwardDataFlow(calledMethod, curValueBox, null, null, -1, depth + 1);
                                            } else if (invokeExpr.getArgs().contains(curValueBox.getValue())) {
                                                resultFromCallee = forwardDataFlow(calledMethod, curValueBox, null, null, -2, depth + 1);

                                            } else {
                                                Event event = new Event(checkedUnit, curValueBox);
                                                if (!processedEvent.contains(event) && !workList.contains(event))
                                                    workList.add(event);
                                            }
                                        } else if (kind.isAsyncTask()) {
                                            if (curValueBox.getValue() instanceof StaticFieldRef) {
                                                resultFromCallee = forwardDataFlow(calledMethod, curValueBox, null, null, -1, depth + 1);
                                            } else if (invokeExpr.getArgs().contains(curValueBox.getValue())) {
                                                resultFromCallee = forwardDataFlow(calledMethod, curValueBox, null, null, invokeExpr.getArgs().indexOf(curValueBox.getValue()), depth + 1);
                                            } else if (!(invokeExpr instanceof StaticInvokeExpr)) {
                                                Value baseBox = getBaseBox(invokeExpr);
                                                if (baseBox.equals(curValueBox.getValue())) {
                                                    AccessPathTag accessPath = (AccessPathTag) curValueBox.getTag("AccessPath");
                                                    if (accessPath.getFieldLength() == 0) {
                                                        resultFromCallee = forwardDataFlow(calledMethod, curValueBox, null, null, -3, depth + 1);
                                                    } else {
                                                        resultFromCallee = forwardDataFlow(calledMethod, curValueBox, null, null, -2, depth + 1);
                                                    }
                                                }
                                            }

                                        } else if (kind == Kind.HANDLER) {
                                        }
                                    }
                                    else if (kind.toString().equals("CALLBACK")) {
                                        if (isValueUsedInUnit(checkedUnit, curValueBox.getValue())) {
                                            resultFromCallee = forwardDataFlow(calledMethod, curValueBox, null, null, 0, depth + 1);
                                        } else if (curValueBox.getValue() instanceof StaticFieldRef) {
                                            resultFromCallee = forwardDataFlow(calledMethod, curValueBox, null, null, -1, depth + 1);
                                        }
                                    } else if (kind.isExplicit()) {
                                        if (curValueBox.getValue() instanceof StaticFieldRef) {
                                            resultFromCallee = forwardDataFlow(calledMethod, curValueBox, null, null, -1, depth + 1);
                                        } else if (invokeExpr.getArgs().contains(curValueBox.getValue())) {
                                            resultFromCallee = forwardDataFlow(calledMethod, curValueBox, null, null, invokeExpr.getArgs().indexOf(curValueBox.getValue()), depth + 1);
                                        } else if (!(invokeExpr instanceof StaticInvokeExpr)) {
                                            Value baseBox = getBaseBox(invokeExpr);
                                            if (baseBox.equals(curValueBox.getValue())) {
                                                AccessPathTag accessPath = (AccessPathTag) curValueBox.getTag("AccessPath");
                                                if (accessPath.getFieldLength() == 0) {
                                                    resultFromCallee = forwardDataFlow(calledMethod, curValueBox, null, null, -3, depth + 1);
                                                } else {
                                                    resultFromCallee = forwardDataFlow(calledMethod, curValueBox, null, null, -2, depth + 1);
                                                }
                                            }
                                        }
                                    }

                                    if (resultFromCallee == null)
                                        continue;

                                    // is important for the processing of the information returned by the call point
                                    for (ValueBox valueMatter : resultFromCallee) {
                                        //It could be a parameter, it could be a return value, it could be a static field, it could be an instance field of this object
                                        if (valueMatter.getTag("Param") != null) {
                                            int index = getArgumentIndex(calledMethod, valueMatter.getValue());
                                            if(index==-1)
                                                continue;
                                            ValueBox argBox = invokeExpr.getArgBox(index);
                                            argBox.addTag(new AccessPathTag(valueMatter.getTag("AccessPath")));
                                            Event event = new Event(checkedUnit, argBox);
                                            if (!processedEvent.contains(event) && !workList.contains(event))
                                                workList.add(event);
                                        } else if (valueMatter.getTag("This") != null) {
                                            Event event = new Event(checkedUnit, curValueBox);
                                            if (!processedEvent.contains(event) && !workList.contains(event))
                                                workList.add(event);
                                        } else if (valueMatter.getTag("StaticField") != null) {
                                            Event event = new Event(checkedUnit, valueMatter);
                                            if (!processedEvent.contains(event) && !workList.contains(event))
                                                workList.add(event);
                                        } else if (valueMatter.getTag("InstanceField") != null) {
                                            Value baseBox = getBaseBox(invokeExpr);
                                            if(baseBox==null)
                                                continue;
                                            VariableBox variableBox = new VariableBox(baseBox);
                                            variableBox.addTag(valueMatter.getTag("AccessPath"));
                                            HashSet<ValueBox> valueBoxes = onDemandBackWardAliasAnalyze(method, variableBox, checkedUnit);

                                            variableBox.addTag(instanceFieldTag);
                                            valueBoxes.add(variableBox);
                                            for (ValueBox alias : valueBoxes) {
                                                Event event = new Event(checkedUnit, alias);
                                                if (!processedEvent.contains(event) && !workList.contains(event))
                                                    workList.add(event);
                                            }
                                        } else if (valueMatter.getTag("RetValue") != null) {
                                            if (checkedUnit instanceof AssignStmt) {
                                                AssignStmt assignStmt = (AssignStmt) checkedUnit;
                                                AccessPathTag accessPath = new AccessPathTag(valueMatter.getTag("AccessPath"));
                                                ValueBox retBox = assignStmt.getDefBoxes().get(0);
                                                retBox.addTag(accessPath);
                                                Event event = new Event(checkedUnit, retBox);
                                                if (!processedEvent.contains(event) && !workList.contains(event))
                                                    workList.add(event);
                                            }
                                        }
                                    }
                                }
                            }
                        } else {
                            Event transferValue = new Event(checkedUnit, curValueBox);
                            if (!processedEvent.contains(transferValue) && !workList.contains(transferValue))
                                workList.add(transferValue);
                        }
                    }
                    else if (checkedUnit instanceof AssignStmt) {
                        // We require that the contamination variable be in the form of a variable name plus its access path 
                        // For example, varName=r1,access path=.filedx.fieldy, indicates that the reference points to the object's fieldx.fieldy is contaminated 
                        //3. If it is a general assignment statement
                        AssignStmt assignStmt = (AssignStmt) checkedUnit;

                        //We need to deal with alias analysis here, but we only deal with alias analysis within a method

                        Value leftOp = assignStmt.getLeftOp();
                        Value rightOp = assignStmt.getRightOp();
                        ValueBox leftBox = assignStmt.getDefBoxes().get(0);

                        Event transferValue = new Event(checkedUnit, curValueBox);
                        if (!processedEvent.contains(transferValue) && !workList.contains(transferValue)) {
                            workList.add(transferValue);
                        }

                        if ((leftOp instanceof InstanceFieldRef) && isUsedInRightOp(checkedUnit, curValueBox.getValue())) {
                
                            InstanceFieldRef instanceFieldRef = (InstanceFieldRef) leftOp;
                            AccessPathTag accessPath = new AccessPathTag(curValueBox.getTag("AccessPath"));
                            accessPath.appendAccessPath(instanceFieldRef.getField().getName());
                            VariableBox variableBox = new VariableBox(instanceFieldRef.getBase());
                            variableBox.addTag(accessPath);
                            variableBox.addTag(instanceFieldTag);
                            transferGlobalValue(accessPath.getFieldChain(),instanceFieldRef.getField());
                            HashSet<ValueBox> aliasValueSet = onDemandBackWardAliasAnalyze(method, variableBox, checkedUnit);//获得变量的别名信息
                            aliasValueSet.add(variableBox);
                            for (ValueBox alias : aliasValueSet) {
                                Event event = new Event(checkedUnit, alias);
                                if (!processedEvent.contains(event) && !workList.contains(event))
                                    workList.add(event);

                            }
                        }
                        else if ((leftOp instanceof StaticFieldRef) && isUsedInRightOp(checkedUnit, curValueBox.getValue())) {
                            leftBox.addTag(new AccessPathTag(curValueBox.getTag("AccessPath")));
                            leftBox.addTag(staticFiledTag);
                            Event event = new Event(checkedUnit, leftBox);
                            if (!processedEvent.contains(event) && !workList.contains(event)) {
                                workList.add(event);
                            }
                            //Handling global variables
                            transferGlobalValue(((AccessPathTag)curValueBox.getTag("AccessPath")).getFieldChain(),((StaticFieldRef)leftOp).getField());

                        }
                        else if ((rightOp instanceof StaticFieldRef) && isUsedInRightOp(checkedUnit, curValueBox.getValue())) {
                            leftBox.addTag(new AccessPathTag(curValueBox.getTag("AccessPath")));
                            Event event = new Event(checkedUnit, leftBox);
                            if (!processedEvent.contains(event) && !workList.contains(event)) {
                                workList.add(event);
                            }
                        }
                        else if ((rightOp instanceof InstanceFieldRef) && isUsedInRightOp(checkedUnit, curValueBox.getValue())) {
                            AccessPathTag accessPath = (AccessPathTag) curValueBox.getTag("AccessPath");
                            InstanceFieldRef fieldRef = (InstanceFieldRef) rightOp;
                            if (accessPath.match(fieldRef.getField().getName())) {
                                AccessPathTag accessPath1 = new AccessPathTag(accessPath);
                                accessPath1.removeAccessPath();
                                leftBox.addTag(accessPath1);
                                Event event = new Event(checkedUnit, leftBox);
                                if (!processedEvent.contains(event) && !workList.contains(event))
                                    workList.add(event);
                            }
                        }
                        else if ((leftOp instanceof ArrayRef) && isUsedInRightOp(checkedUnit, curValueBox.getValue())) {
                            ArrayRef arrayRef = (ArrayRef) leftOp;
                            ValueBox baseBox = arrayRef.getBaseBox();
                            baseBox.addTag(curValueBox.getTag("AccessPath"));
                            Event event = new Event(checkedUnit, baseBox);
                            if (!processedEvent.contains(event) && !workList.contains(event))
                                workList.add(event);
                        }
                        else if ((rightOp instanceof ArrayRef) && isUsedInRightOp(checkedUnit, curValueBox.getValue())) {
                            //array load, y=taint[i]
                            leftBox.addTag(curValueBox.getTag("AccessPath"));
                            Event event = new Event(checkedUnit, leftBox);
                            if (!processedEvent.contains(event) && !workList.contains(event))
                                workList.add(event);
                        }
                        else if ((rightOp instanceof CastExpr) && isUsedInRightOp(checkedUnit, curValueBox.getValue())) {
                            //cast object
                            leftBox.addTag(new AccessPathTag(curValueBox.getTag("AccessPath")));
                            Event event = new Event(checkedUnit, leftBox);
                            if (!processedEvent.contains(event) && !workList.contains(event))
                                workList.add(event);


                        }
                        else if (rightOp.toString().equals(curValueBox.getValue().toString())) {
                            leftBox.addTag(new AccessPathTag(curValueBox.getTag("AccessPath")));
                            Event event = new Event(checkedUnit, leftBox);
                            if (!processedEvent.contains(event) && !workList.contains(event))
                                workList.add(event);
                        }
                        else if (isUsedInRightOp(checkedUnit, curValueBox.getValue())) {
                            leftBox.addTag(new AccessPathTag());
                            Event event = new Event(checkedUnit, leftBox);
                            if (!processedEvent.contains(event) && !workList.contains(event))
                                workList.add(event);
                        }
                    }
                    else {
                        Event event = new Event(checkedUnit, curValueBox);
                        if (!processedEvent.contains(event) && !workList.contains(event))
                            workList.add(event);
                        if(!(checkedUnit instanceof IfStmt))
                            continue;
                        AccessPathTag pathTag = (AccessPathTag) curValueBox.getTag("AccessPath");
                        if(pathTag.getFieldChain().length()>0)
                            continue;
                        IfStmt ifStmt = (IfStmt) checkedUnit;
                        List<ValueBox> useBoxes = ifStmt.getCondition().getUseBoxes();
                        boolean flag=false;
                        for(ValueBox box:useBoxes){
                            if(box.getValue().equals(curValueBox.getValue()))
                                flag=true;
                        }
                        if(!flag)
                            continue;
                        if(checkedIfSet.contains(checkedUnit))
                            continue;
                        checkedIfSet.add(checkedUnit);
                        if(implicitMode){
                            // If it is a conditional statement, we need to focus on where 
                            //1, different branches may trigger to trigger some dangerous calls, only judging from the control flow 
                            //2. Different branches assign different values to different variables, and we think these variables should be contaminated 
                            //3. The data in the condition may be contaminated 
                            //4. Operations on collection classes may be contaminated
                            HashSet<Unit> dependUnits = doWithControlFlowDependentUnit(checkedUnit, curValueBox);
                            if(dependUnits==null||dependUnits.isEmpty())
                                continue;
                            for(Unit dependUnit:dependUnits){
                                if(dependUnit instanceof InvokeStmt){
                                    InvokeExpr invokeExpr = getInvokeExpr(dependUnit);
                                    if(invokeExpr.getMethod().getDeclaringClass().getName().equals("java.util.Iterator")){
                                        Value baseBox = getBaseBox(invokeExpr);
                                        Unit defUnit = getDirectDefUnit(dependUnit, baseBox, method);
                                        InvokeExpr defInvoke = getInvokeExpr(defUnit);
                                        if(defInvoke==null){
                                            logger.info("Iterator is get by indirect way!");
                                            continue;
                                        }

                                        String signature = defInvoke.getMethod().getSignature();
                                        if(signature.equals("<java.util.List: java.util.Iterator iterator()>")){
                                            Value base = getBaseBox(defInvoke);
                                            VariableBox variableBox = new VariableBox(base);
                                            variableBox.addTag(new AccessPathTag());
                                            Event new_event = new Event(dependUnit, variableBox);
                                            if (!processedEvent.contains(new_event) && !workList.contains(new_event))
                                                workList.add(new_event);
                                        }else {
                                            logger.info("Iterator is not build by standard API!");
                                        }

                                    }else {
                                        Value baseBox = getBaseBox(invokeExpr);
                                        VariableBox variableBox = new VariableBox(baseBox);
                                        variableBox.addTag(new AccessPathTag());
                                        Event new_event = new Event(dependUnit, variableBox);
                                        if (!processedEvent.contains(new_event) && !workList.contains(new_event))
                                            workList.add(new_event);
                                    }

                                }else if(dependUnit instanceof AssignStmt){
                                    AssignStmt assignStmt = (AssignStmt) dependUnit;
                                    Value leftOp = assignStmt.getLeftOp();
                                    if(leftOp instanceof Local){
                                        VariableBox variableBox = new VariableBox(leftOp);
                                        variableBox.addTag(new AccessPathTag());
                                        Event new_event = new Event(dependUnit, variableBox);
                                        if (!processedEvent.contains(new_event) && !workList.contains(new_event))
                                            workList.add(new_event);
                                    }else if(leftOp instanceof InstanceFieldRef){
                                        InstanceFieldRef instanceFieldRef = (InstanceFieldRef) leftOp;
                                        AccessPathTag accessPath = new AccessPathTag();
                                        accessPath.appendAccessPath(instanceFieldRef.getField().getName());
                                        VariableBox variableBox = new VariableBox(instanceFieldRef.getBase());
                                        variableBox.addTag(accessPath);
                                        variableBox.addTag(instanceFieldTag);
                                        Event new_event = new Event(dependUnit, variableBox);
                                        if (!processedEvent.contains(new_event) && !workList.contains(new_event))
                                            workList.add(new_event);

                                    }else if(leftOp instanceof StaticFieldRef){
                                        VariableBox variableBox = new VariableBox(leftOp);
                                        variableBox.addTag(new AccessPathTag());
                                        variableBox.addTag(staticFiledTag);
                                        Event new_event = new Event(dependUnit, variableBox);
                                        if (!processedEvent.contains(new_event) && !workList.contains(new_event))
                                            workList.add(new_event);
                                    }
                                }else if(dependUnit instanceof ReturnStmt){
                                    ReturnStmt returnUnit = (ReturnStmt) dependUnit;
                                    ValueBox retBox = returnUnit.getOpBox();
                                    retBox.addTag(retTag);
                                    retBox.addTag(new AccessPathTag());
                                    res.add(retBox);
                                }
                            }
                        }
                    }
                }
            }
        }
        //Returns the information that this method needs to return to the caller
        inputMapOutCache.put(mark, new HashSet<>());
        inputMapOutCache.get(mark).addAll(res);//Data caching
        return res;
    }


    public HashSet<ValueBox> onDemandBackWardAliasAnalyze(SootMethod method, ValueBox valueBox, Unit curUnit) {
        // Backward alias analysis 
        // Take x.ield =taint only if store occurs and we go looking for the alias of x 
        // Here we need to add some collection class operations, for example, when a collection container changes, it is also treated as a store operation 
        // This alias analysis algorithm is not accurate because alias analysis often requires accurate pointer analysis 
        // Our rules are very simple 
        // Direct assignment statements for x are analyzed upward, such as x=y,x= z.iled, and these variables are added directly if they were not refreshed before reaching x.iled =taint 
        // Then it is no longer analyzed, meaning that the alias of y is no longer analyzed, and the accuracy is indeed lost
        HashSet<ValueBox> res = new HashSet<>();
        EventQueue workList = new EventQueue();
        workList.add(new Event(curUnit, valueBox));
        HashSet<Event> processedEvent = new HashSet<>();
        BriefUnitGraph graph = new BriefUnitGraph(method.retrieveActiveBody());

        while (!workList.isEmpty()) {
            Event poll = workList.poll();
            Unit unit = poll.unit;
            ValueBox defineBox = poll.valueBox;
            processedEvent.add(poll);
            for (Unit preUnit : graph.getPredsOf(unit)) {
                if (isValueDefinedOrUsedInUnit(preUnit, defineBox.getValue())) {

                    if (isValueDefinedInUnit(preUnit, defineBox.getValue())) {
                        if (preUnit instanceof AssignStmt) {
                            AssignStmt assignStmt = (AssignStmt) preUnit;
                            Value rightOp = assignStmt.getRightOp();
                            ValueBox rightOpBox = assignStmt.getRightOpBox();
                            if (rightOp instanceof Local) {
                                rightOpBox.addTag(new AccessPathTag(valueBox.getTag("AccessPath")));
                                res.add(rightOpBox);
                            } else if (rightOp instanceof InstanceFieldRef) {
                                InstanceFieldRef instanceFieldRef = (InstanceFieldRef) rightOp;
                                Value base = instanceFieldRef.getBase();
                                VariableBox variableBox = new VariableBox(base);
                                AccessPathTag accessPathTag = new AccessPathTag(valueBox.getTag("AccessPath"));
                                accessPathTag.appendAccessPath(instanceFieldRef.getField().getName());
                                variableBox.addTag(accessPathTag);
                                variableBox.addTag(instanceFieldTag);
                                res.add(variableBox);
                            } else if (rightOp instanceof StaticFieldRef) {
                                rightOpBox.addTag(new AccessPathTag(valueBox.getTag("AccessPath")));
                                rightOpBox.addTag(staticFiledTag);
                                res.add(rightOpBox);
                            } else if (rightOp instanceof CastExpr) {
                                CastExpr castExpr = (CastExpr) rightOp;
                                Value op = castExpr.getOp();
                                VariableBox variableBox = new VariableBox(op);
                                variableBox.addTag(new AccessPathTag(valueBox.getTag("AccessPath")));
                                res.add(variableBox);
                            }
                        }
                    } else {
                        Event event = new Event(preUnit, defineBox);
                        if (!workList.contains(event) && !processedEvent.contains(event))
                            workList.add(event);
                    }
                } else {
                    Event event = new Event(preUnit, defineBox);
                    if (!workList.contains(event) && !processedEvent.contains(event))
                        workList.add(event);
                }
            }
        }
        return res;
    }

    public static boolean isSystemClass(String clsName) {
        if (clsName.startsWith("java.") || clsName.startsWith("javax."))
            return true;
        if (clsName.startsWith("android.") || clsName.startsWith("androidx.") || clsName.startsWith("com.google."))
            return true;
        if (clsName.startsWith("jdk"))
            return true;
        if (clsName.startsWith("sun."))
            return true;
        if (clsName.startsWith("org.omg") || clsName.startsWith("org.w3c.dom"))
            return true;
        return false;
    }

    private Unit getArgumentsAssignment(SootMethod method, int paramIndex) {
        for (Unit unit : method.retrieveActiveBody().getUnits()) {
            if (unit instanceof IdentityStmt)
                if (unit.toString().contains("@parameter" + paramIndex + ":"))
                    return unit;
        }
        return null;
    }

    private int getArgumentIndex(SootMethod method, Value value) {
        for (Unit u : method.retrieveActiveBody().getUnits()) {
            if (u instanceof IdentityStmt) {
                if (isValueDefinedInUnit(u, value)) {
                    IdentityStmt identityStmt = (IdentityStmt) u;
                    Value rightOp = identityStmt.getRightOp();
                    if(rightOp instanceof ParameterRef) {
                        ParameterRef parameterRef = (ParameterRef) rightOp;
                        return parameterRef.getIndex();
                    }
                }
            }
        }
        return -1;
    }

    private Value getBaseBox(InvokeExpr invokeExpr) {
        Value res = null;
        if (invokeExpr instanceof VirtualInvokeExpr)
            res = ((VirtualInvokeExpr) invokeExpr).getBaseBox().getValue();
        else if (invokeExpr instanceof SpecialInvokeExpr)
            res = ((SpecialInvokeExpr) invokeExpr).getBaseBox().getValue();
        else if (invokeExpr instanceof InterfaceInvokeExpr)
            res = ((InterfaceInvokeExpr) invokeExpr).getBaseBox().getValue();
        return res;
    }

    //Determines whether the variable is used in the statement
    public static boolean isValueUsedInUnit(Unit unit, Value value) {
        List<String> usedValue = new ArrayList<>();
        for (ValueBox useBox : unit.getUseBoxes()) {
            usedValue.add(useBox.getValue().toString());
        }
        return usedValue.contains(value.toString());
    }

    //Determines whether the variable is defined in the statement
    public static boolean isValueDefinedInUnit(Unit unit, Value value) {
        if(!(unit instanceof IdentityStmt)&&!(unit instanceof AssignStmt))
            return false;
        for(ValueBox useBox:unit.getUseBoxes()){
            if(useBox.getValue().equals(value))
                return false;
        }
        for (ValueBox defBox : unit.getDefBoxes()) {
            if(defBox.getValue().equals(value))
                return true;
        }
        return false;
    }

    public static boolean isValueDefinedOrUsedInUnit(Unit unit, Value value) {
        for (ValueBox valueBox : unit.getUseAndDefBoxes()) {
            if (valueBox.getValue().toString().equals(value.toString()))
                return true;
        }
        return false;
    }

    //    public static boolean isInRight
    public static boolean isUsedInRightOp(Unit unit, Value value) {
        if (!(unit instanceof AssignStmt))
            return false;
        AssignStmt assignStmt = (AssignStmt) unit;
        ValueBox rightOpBox = assignStmt.getRightOpBox();
        Queue<ValueBox> queue = new LinkedList<>();
        queue.add(rightOpBox);
        while (!queue.isEmpty()) {
            ValueBox poll = queue.poll();
            if (poll.getValue().equals(value))
                return true;
            queue.addAll(poll.getValue().getUseBoxes());
        }
        return false;
    }

    public boolean isMethodCanAffectHeap(String methodName) {
        String[] methodNameList = {"add", "addAll", "put", "putAll"};
        for (String name : methodNameList) {
            if (name.equals(methodName))
                return true;
        }
        return false;
    }

    public void preAnalysis() {
        // Preprocessing collects some information in the application 
        // Handle the mapping of static fields and their load points in the application 
        // Handle the mapping of singleton fields and their load points in the application
        ReachableMethods reachableMethods = Scene.v().getReachableMethods();
        QueueReader<MethodOrMethodContext> listener = reachableMethods.listener();
        HashSet<SootClass> singleTonClasses=new HashSet<>();
        for(SootClass cls:Scene.v().getApplicationClasses()){
            if(isSingleTonCls(cls))
                singleTonClasses.add(cls);
        }
        while (listener.hasNext()) {
            MethodOrMethodContext method = listener.next();
            SootMethod m = method.method();
            if (m.isConcrete()) {
                try {
                    Body body = m.retrieveActiveBody();
                    for (Unit unit : body.getUnits()) {
                        if (unit instanceof AssignStmt) {
                            AssignStmt assignStmt = (AssignStmt) unit;
                            Value rightOp = assignStmt.getRightOp();
                            if (rightOp instanceof StaticFieldRef) {
                                SootField field = ((StaticFieldRef) rightOp).getField();
                                if (!staticField2MapLoadSite.containsKey(field)) {
                                    staticField2MapLoadSite.put(field, unit);
                                } else {
                                    staticField2MapLoadSite.get(field).add(unit);
                                }
                            }else if(rightOp instanceof InstanceFieldRef){
                                SootField field = ((InstanceFieldRef) rightOp).getField();
                                if(singleTonClasses.contains(field.getDeclaringClass())){
                                    if(!singleTonFieldMap2LoadSite.containsKey(field)){
                                        singleTonFieldMap2LoadSite.put(field,unit);
                                    }else {
                                        singleTonFieldMap2LoadSite.get(field).add(unit);
                                    }
                                }
                            }
                        }
                    }
                }catch (Exception e){
                    e.printStackTrace();
                }
            }
        }
    }

    private void transferGlobalValue(String accessPath,SootField field){
        if(!isTrackGlobalTaintValue)
            return;
        if(tracedGlobalTaintValue.contains(field)){
            logger.info("The global value has been done!");
            return;
        }
        tracedGlobalTaintValue.add(field);

        logger.info("track for global taint value ...");
        if(field.isStatic()&&staticField2MapLoadSite.containsKey(field)){
            for(Unit loaderSite:staticField2MapLoadSite.get(field)){
                SootMethod m = icfg.getMethodOf(loaderSite);
                runFlowAnalysis(m,loaderSite,accessPath);
            }
        }else if(!field.isStatic()&&singleTonFieldMap2LoadSite.containsKey(field)) {
            for (Unit loaderSite : singleTonFieldMap2LoadSite.get(field)) {
                SootMethod m = icfg.getMethodOf(loaderSite);
                logger.info("[Global Value Load Site]: {}", loaderSite);
                runFlowAnalysis(m, loaderSite, accessPath);
            }
        }
    }


    public HashSet<Unit> doWithControlFlowDependentUnit(Unit u,ValueBox curValueBox){
        //Handles issues related to control flow dependencies
        SootMethod methodOf = icfg.getMethodOf(u);
        if(methodOf==null)
            return new HashSet<>();
        DirectedGraph<Unit> graph = icfg.getOrCreateUnitGraph(icfg.getMethodOf(u));
        MHGPostDominatorsFinder<Unit> postdominatorFinder = new MHGPostDominatorsFinder<Unit>(graph);
        Unit postdom = postdominatorFinder.getImmediateDominator(u);
        HashSet<SootMethod> dependMethods = getAllCallDependCondition(u, postdom);

        HashSet<Unit> res=new HashSet<>();
        if(postdom==null&&isPrimitiveType(icfg.getMethodOf(u).getReturnType())) {
            HashSet<Unit> returnUnit = getAllReturnUnit(graph);
            res.addAll(returnUnit);
        }
        for(SootMethod dependMethod:dependMethods){
            checker.isDependConditionSink(dependMethod,icfg.getMethodOf(u));
        }
        return res;
    }

    public void buildPaths(Unit end,Unit curUnit,DirectedGraph<Unit> graph,List<Unit> path,List<List<Unit>> res){
        if(curUnit!=null&&curUnit.equals(end)){
            ArrayList<Unit> addPath = new ArrayList<>(path);
            addPath.add(curUnit);
            res.add(addPath);
            return;
        }
        if(!path.contains(curUnit)) {
            path.add(curUnit);
        }else {
            return;
        }
        for(Unit nextUnit:graph.getSuccsOf(curUnit)){
            buildPaths(end,nextUnit,graph,new ArrayList<>(path),res);
        }

    }

    public HashSet<Unit> getAllReturnUnit(DirectedGraph<Unit> graph){
        HashSet<Unit> res=new HashSet<>();
        for(Unit returnUnit:graph.getTails()){
            if(returnUnit instanceof ReturnStmt){
                ReturnStmt returnStmt = (ReturnStmt) returnUnit;
                Value op = returnStmt.getOp();
                if(op instanceof NullConstant)
                    continue;
                res.add(returnStmt);

            }
        }
        return res;
    }


    public HashSet<SootMethod> getAllCallDependCondition(Unit beginUnit,Unit endUnit){
        HashSet<SootMethod> res=new HashSet<>();
        if(!(beginUnit instanceof IfStmt)) {
            logger.info("{} is not an IfStmt!", beginUnit);
            return res;
        }

        for(Unit unit:icfg.getSuccsOf(beginUnit)){
            HashSet<SootMethod> ans = getMethodByBFS(unit, endUnit);
            if(res.size()==0){
                res.addAll(ans);
            }else {
                makeIntersection(res,ans);
            }

        }
        return res;
    }

    public HashSet<SootMethod> getMethodByBFS(Unit start,Unit endUnit){
        Queue<Unit> queue=new LinkedList<>();
        HashSet<Unit> visit=new HashSet<>();
        HashSet<SootMethod> res=new HashSet<>();
        queue.add(start);
        while (!queue.isEmpty()){
            Unit poll = queue.poll();
            visit.add(poll);
            InvokeExpr invokeExpr = getInvokeExpr(poll);
            if(invokeExpr!=null){
                res.add(icfg.getMethodOf(poll));
            }
            if(poll.equals(endUnit))
                continue;
            for(Unit succUnit:icfg.getSuccsOf(poll)){
                if(visit.contains(succUnit))
                    continue;
                queue.add(succUnit);
            }

        }
        return res;
    }

    public HashSet<SootMethod> makeIntersection(HashSet<SootMethod> a,HashSet<SootMethod> b){
        HashSet<SootMethod> temp = new HashSet<>(a);
        a.retainAll(b);
        temp.addAll(b);
        temp.removeAll(a);
        return temp;
    }

    public HashSet<Unit> makeIntersectionValue(HashSet<Unit> a,HashSet<Unit> b){
        HashSet<Unit> temp = new HashSet<>(a);
        a.retainAll(b);
        temp.addAll(b);
        temp.removeAll(a);
        return temp;
    }



    public HashSet<Unit> getAllValueDependCondition(Unit beginUnit,Unit endUnit){
        HashSet<Unit> res=new HashSet<>();
        if(!(beginUnit instanceof IfStmt)) {
            logger.info("{} is not an IfStmt!", beginUnit);
            return res;
        }

        for(Unit unit:icfg.getSuccsOf(beginUnit)){
            HashSet<Unit> ans = getValueByBFS(unit, endUnit);
            if(res.size()==0){
                res.addAll(ans);
            }else {
                makeIntersectionValue(res,ans);
            }

        }
        return res;
    }

    public HashSet<Unit> getValueByBFS(Unit start,Unit endUnit){
        Queue<Unit> queue=new LinkedList<>();
        HashSet<Unit> visit=new HashSet<>();
        HashSet<Unit> res=new HashSet<>();
        queue.add(start);
        while (!queue.isEmpty()){
            Unit poll = queue.poll();
            visit.add(poll);
            if(poll instanceof AssignStmt){
                AssignStmt assignStmt = (AssignStmt) poll;
                Value rightOp = assignStmt.getRightOp();
                if(!(rightOp instanceof InvokeExpr)&&isPrimitiveType(rightOp.getType())) {
                    res.add(poll);
                }
            }
            if(poll.equals(endUnit))
                continue;
            for(Unit succUnit:icfg.getSuccsOf(poll)){
                if(visit.contains(succUnit))
                    continue;
                queue.add(succUnit);
            }

        }
        return res;
    }




    public static Unit getDirectDefUnit(Unit curUnit,Value value,SootMethod method){
        if (!method.isConcrete())
            return null;
        BriefUnitGraph graph = new BriefUnitGraph(method.retrieveActiveBody());
        Queue<Unit> queue = new LinkedList<>();
        queue.add(curUnit);
        HashSet<Unit> visit = new HashSet<>();
        while (!queue.isEmpty()) {
            Unit poll = queue.poll();
            visit.add(poll);
            if (isValueDefinedInUnit(poll, value))
                return poll;
            for (Unit pre : graph.getPredsOf(poll)) {
                if (!visit.contains(pre))
                    queue.add(pre);
            }
        }
        return null;

    }

    private boolean isPrimitiveType(Type type){
        if(type.toString().equals("boolean")||type.toString().equals("int")||type.toString().equals("float")||type.toString().equals("double")||type.toString().equals("long"))
            return true;
        return false;

    }

    public static boolean isSingleTonCls(SootClass cls){
        if(cls.isEnum()||cls.isInterface()||cls.isAbstract()||cls.isInnerClass()||cls.isPrivate())
            return false;
        if(isSystemClass(cls.getName()))
            return false;
        boolean flag=true;
        for(SootMethod m:cls.getMethods()){
            if(m.getName().equals("<init>")&&!m.isPrivate())
                flag=false;

        }
        return flag;



    }



}




