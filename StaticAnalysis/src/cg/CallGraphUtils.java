package cg;

import constant.StrawPointsDefinition;
import dataflow.CallSite;
import javafx.scene.Scene;
import javafx.util.Pair;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.*;
import soot.jimple.*;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.jimple.toolkits.callgraph.ReachableMethods;
import soot.options.Options;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.DirectedGraph;
import soot.util.queue.QueueReader;
import util.Log;
import util.StringUtil;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.lang.reflect.Constructor;
import java.util.*;

/**
 * @program: Ditto
 * @description: Provide basic functions for building call graphs.
 **/
public class CallGraphUtils {

    private static final Logger logger = LoggerFactory.getLogger(CallGraphUtils.class);

    public static final String SPARK = "spark";
    public static final String CHA = "cha";
    public static final String RTA = "rta";
    public static final String VTA = "vta";

    private static HashSet<String> customizedEndpoints = new HashSet<>();


    private static void resetCallGraph() {
        Scene.v().releaseCallGraph();
        Scene.v().releasePointsToAnalysis();
        Scene.v().releaseReachableMethods();
        G.v().resetSpark();
    }

    public static void constructCallGraphConfig(String callgraphAlgorithm) {
        switch (callgraphAlgorithm) {
            case SPARK:
                Options.v().setPhaseOption("cg.spark", "on");
                break;
            case CHA:
                Options.v().setPhaseOption("cg.cha", "on");
                break;
            case RTA:
                Options.v().setPhaseOption("cg.spark", "on");
                Options.v().setPhaseOption("cg.spark", "rta:true");
                Options.v().setPhaseOption("cg.spark", "on-fly-cg:false");
                break;
            case VTA:
                Options.v().setPhaseOption("cg.spark", "on");
                Options.v().setPhaseOption("cg.spark", "vta:true");
                break;
            default:
                throw new RuntimeException("Invalid callgraph algorithm");
        }
    }

    public static void constructCallGraph(String callgraphAlgorithm) {
        resetCallGraph();
        constructCallGraphConfig(callgraphAlgorithm);
        PackManager.v().getPack("cg").apply();
    }

    public static boolean reachable(SootMethod method) {
        ReachableMethods reachableMethods = Scene.v().getReachableMethods();
        return reachableMethods.contains(method);
    }

    public static boolean isMethodReachable2Target(SootMethod begin, String targetMethod) {
        QueueReader<MethodOrMethodContext> listener =
                Scene.v().getReachableMethods().listener();
        while (listener.hasNext()) {
            String subSignature = listener.next().method().getSubSignature();
            if (targetMethod.equals(subSignature))
                return true;
        }
        return false;
    }

    public static HashMap<SootMethod, Unit> findTargetMethodInvokeInICFG(SootMethod method, String targetMethod) {
        //Find statements in ICFG that satisfy the condition
        HashMap<SootMethod, Unit> res = new HashMap<>();
        QueueReader<MethodOrMethodContext> listener =
                Scene.v().getReachableMethods().listener();
        SootMethod target = null;
        while (listener.hasNext()) {
            SootMethod sootMethod = listener.next().method();
            if (sootMethod.getSubSignature().equals(targetMethod)) {
                target = sootMethod;
                break;
            }
        }
        Iterator<Edge> edges = Scene.v().getCallGraph().edgesInto(target);
        while (edges.hasNext()) {
            SootMethod m = edges.next().getTgt().method();
            if (m.isConcrete()) {
                for (Unit unit : m.retrieveActiveBody().getUnits()) {
                    if (unit instanceof AssignStmt) {
                        AssignStmt assignStmt = (AssignStmt) unit;
                        if (assignStmt.containsInvokeExpr()) {
                            if (assignStmt.getInvokeExpr().getMethod().getSubSignature().equals(targetMethod)) {
                                res.put(m, unit);
                            }
                        }
                    }
                }
            }
        }
        return res;

    }


    //Used to find all call paths from entrypoint to the target method
    public static void findTargetMethod(SootMethod method, HashSet<String> targetMethod, String mode, List<CallSite> callStack, int max_depth, int depth, HashSet<List<CallSite>> paths) {
        if (!Scene.v().hasCallGraph())
            throw new RuntimeException("No CallGraph in Scence");
        if (depth > max_depth)
            return;
        for (CallSite callSite : callStack) {
            if (callSite.caller.getSignature().equals(method.getSignature()))
                return;
        }
        if (mode.equals("Signature") && targetMethod.contains(method.getSignature())) {
            logger.info("找到相关调用");
            paths.add(callStack);
        } else if (mode.equals("SubSignature") && targetMethod.contains(method.getSubSignature())) {
            logger.info("找到相关调用");
            paths.add(callStack);
        }
        CallGraph callGraph = Scene.v().getCallGraph();
        Iterator<Edge> edgeIterator = callGraph.edgesOutOf(method);
        while (edgeIterator.hasNext()) {

            Edge next = edgeIterator.next();
            List<CallSite> addedCallStack = new ArrayList<>(callStack);
            addedCallStack.add(new CallSite(next.src(), next.srcUnit(), -1));
            findTargetMethod(next.tgt(), targetMethod, mode, addedCallStack, max_depth, depth + 1, paths);
        }
    }

    //Used to find all call paths from target method to the entrypoint
    public static void findEntryMethod(SootMethod method, HashSet<String> entryMethod, String mode, List<CallSite> callStack, int max_depth, int depth, HashSet<List<CallSite>> paths, boolean isMustFoundEntry) {
        //Prunning
        if (!Scene.v().hasCallGraph())
            throw new RuntimeException("No CallGraph in Scene");
        if (method.getSubSignature().equals("void run()") && method.getDeclaringClass().getSuperclass().getName().equals("java.lang.Object"))
            return;
        if (depth > max_depth) {
            if (!isMustFoundEntry)
                paths.add(callStack);
            return;
        }
        if (mode.equals("Signature") && entryMethod.contains(method.getSignature())) {
            paths.add(callStack);
            return;
        } else if (mode.equals("SubSignature") && entryMethod.contains(method.getSubSignature())) {
            paths.add(callStack);
            return;
        }
        CallGraph callGraph = Scene.v().getCallGraph();
        Iterator<Edge> edgeIterator = callGraph.edgesInto(method);
        while (edgeIterator.hasNext()) {
            Edge next = edgeIterator.next();
            List<CallSite> addedCallStack = new ArrayList<>(callStack);
            //Check for loop
            if (callStack.contains(new CallSite(next.src(), next.srcUnit(), -1)))
                continue;
            addedCallStack.add(new CallSite(next.src(), next.srcUnit(), -1));
            findEntryMethod(next.src(), entryMethod, mode, addedCallStack, max_depth, depth + 1, paths, isMustFoundEntry);
        }
    }

    // The DFS algorithm traverses the CG, finding all the paths from method A to method B and saving them in accessPaths to return
    public static boolean dfs(CallGraph callGraph, SootMethod begin, String targetMethod, int max_depth, HashSet<List<SootMethod>> accessPaths) {
        boolean isAccessable = false;
        ArrayList<SootMethod> accessPath = new ArrayList<>();
        int depth = 1;
        Stack<Pair> callstacks = new Stack<>();
        callstacks.push(new Pair(new CallSite(begin,null,-1),depth));
        HashSet<String> visited = new HashSet<>();

        if (!Scene.v().hasCallGraph())
            throw new RuntimeException("No CallGraph in Scene");

        while(!callstacks.isEmpty()){
            Pair cp = callstacks.pop();
            CallSite cs = (CallSite) cp.getKey();
            SootMethod sm = cs.caller;
            int currentDepth = (int) cp.getValue();
            if(!accessPath.isEmpty()){
                SootMethod lstMethod = accessPath.get(accessPath.size()-1);
                while(!isCaller(callGraph,lstMethod,sm)){
                    accessPath.remove(lstMethod);
                    lstMethod = accessPath.get(accessPath.size()-1);
                }
            }
            accessPath.add(sm);
            if(sm.getSignature().equals(targetMethod)){
                visited.remove(sm.getSignature());
                accessPaths.add(new ArrayList<>(accessPath));
                isAccessable = true;
                accessPath.remove(sm);
                continue;
            }

            Iterator<Edge> edgeIterator = callGraph.edgesOutOf(sm);

            if(currentDepth < max_depth && edgeIterator.hasNext()) {
                boolean hasNewEdge = false;
                while (edgeIterator.hasNext()) {
                    Edge next = edgeIterator.next();
                    if(visited.contains(next.tgt().getSignature()))
                        continue;
                    callstacks.push(new Pair(new CallSite(next.tgt(), next.srcUnit(),-1),currentDepth+1));
                    visited.add(next.tgt().getSignature());
                    hasNewEdge = true;
                }
                if(!hasNewEdge)
                    accessPath.remove(sm);
            }else{
                accessPath.remove(sm);
            }
        }
        return isAccessable;
    }

    public static boolean dfsV2(CallGraph callGraph, SootMethod begin, String targetMethod, int max_depth, HashSet<List<CallSite>> accessPaths) {
        boolean isAccessable = false;
        List<CallSite> accessPath = new ArrayList<>();
        int depth = 1;
        Stack<Pair> callstacks = new Stack<>();
        callstacks.push(new Pair(new CallSite(null,begin,null,-1),depth));
        HashSet<String> visited = new HashSet<>();

        if (!Scene.v().hasCallGraph())
            throw new RuntimeException("No CallGraph in Scene");

        while(!callstacks.isEmpty()){
            Pair cp = callstacks.pop();
            CallSite cs = (CallSite) cp.getKey();
            SootMethod sm = cs.callee;
            int currentDepth = (int) cp.getValue();
            if(!accessPath.isEmpty()){
                CallSite lastsite = accessPath.get(accessPath.size()-1);
                while(!accessPath.isEmpty() && !isCaller(callGraph,lastsite.callee,sm)){
                    accessPath.remove(accessPath.size()-1);
                    try {
                        lastsite = accessPath.get(accessPath.size()-1);
                    }catch (Exception e){
                        System.out.println(e);
                        logger.info(callstacks.toString());
                        logger.info(accessPaths.toString());
                    }
                }
            }
            accessPath.add(cs);
            if(sm.getSignature().equals(targetMethod)){
                visited.remove(sm.getSignature());
                accessPaths.add(new ArrayList<>(accessPath));
                isAccessable = true;
                accessPath.remove(accessPath.lastIndexOf(cs));
                continue;
            }

            Iterator<Edge> edgeIterator = callGraph.edgesOutOf(sm);

            if(currentDepth < max_depth && edgeIterator.hasNext()) {
                boolean hasNewEdge = false;
                while (edgeIterator.hasNext()) {
                    Edge next = edgeIterator.next();
                    if(visited.contains(next.tgt().getSignature()))
                        continue;
                    callstacks.push(new Pair(new CallSite(next.src(),next.tgt(), next.srcUnit(),-1),currentDepth+1));
                    visited.add(next.tgt().getSignature());
                    hasNewEdge = true;
                }
                if(!hasNewEdge)
                    accessPath.remove(accessPath.lastIndexOf(cs));
            }else{
                accessPath.remove(accessPath.lastIndexOf(cs));
            }
        }
        return isAccessable;
    }

    public static boolean isCaller(CallGraph cg, SootMethod a, SootMethod b){
        Iterator<Edge> edgeIterator = cg.edgesOutOf(a);
        while(edgeIterator.hasNext()){
            Edge next = edgeIterator.next();
            if (next.tgt().equals(b))
                return  true;
        }
        return false;
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

    public static CallGraph cg=null;

    public static void buildCGbyCHA(List<SootMethod> entrypoints) {
        Queue<SootMethod> worklist = new LinkedList<>(entrypoints);
        HashSet<SootMethod> reachableMethod = new HashSet<>();
        cg = new CallGraph();
        Scene.v().setEntryPoints(entrypoints);
        while (!worklist.isEmpty()) {
            SootMethod poll = worklist.poll();
            if (reachableMethod.contains(poll))
                continue;
            reachableMethod.add(poll);

            if (isSystemClass(poll.getDeclaringClass().getName())||isThirdPartyLibrary(poll.getDeclaringClass().getName()))
                continue;
            if (poll.isPhantom())
                continue;
            if (poll.isNative())
                continue;
            if (!poll.isConcrete())
                continue;
            try {
                for (Unit u : poll.retrieveActiveBody().getUnits()) {
                    InvokeExpr invokeExpr = null;
                    if (u instanceof InvokeStmt) {
                        InvokeStmt invokeStmt = (InvokeStmt) u;
                        invokeExpr = invokeStmt.getInvokeExpr();
                    }

                    if (u instanceof AssignStmt) {
                        AssignStmt assignStmt = (AssignStmt) u;
                        if (assignStmt.containsInvokeExpr())
                            invokeExpr = assignStmt.getInvokeExpr();
                    }

                    if (invokeExpr == null)
                        continue;

                    Kind kind = Kind.STATIC;

                    HashSet<SootMethod> targetMethods = new HashSet<>();

                    if (invokeExpr instanceof StaticInvokeExpr) {
                        targetMethods.add(invokeExpr.getMethod());
                        kind = Kind.STATIC;
                    } else {
                        int size = invokeExpr.getUseBoxes().size();
                        //Get the interface by getting the Box in the first position --------- for Soot-4.6
                        if (invokeExpr instanceof SpecialInvokeExpr) {
                            //Handles instance methods, private methods, or parent methods of this class
                            SootMethod method = invokeExpr.getMethod();
                            if (method != null) {
                                targetMethods.add(method);
                                kind = Kind.SPECIAL;
                            }
                        } else if ((invokeExpr instanceof InterfaceInvokeExpr) || (invokeExpr instanceof VirtualInvokeExpr)) {
                            String name = invokeExpr.getMethod().getName();
                            InstanceInvokeExpr instanceInvokeExpr = (InstanceInvokeExpr) invokeExpr;
                            Type instancType = instanceInvokeExpr.getBase().getType();
                            SootClass sootClass = Scene.v().getSootClass(instancType.toString());
                            if (!sootClass.hasSuperclass())
                                continue;
                            String superClassName = sootClass.getSuperclass().getName();
                            //There are some special calls that need to be handled in cg, and the concern here is asynchrony
                            if ((name.equals("run") && sootClass.implementsInterface("java.lang.Runnable")) || (name.equals("start") && (superClassName.equals("java.lang.Thread") || sootClass.getName().equals("java.lang.Thread"))) ||
                                    (name.equals("execute")) || (name.equals("post") && superClassName.equals("android.os.Handler"))||name.equals("postDelayed")) {
                                HashMap<SootMethod, Kind> asyncMethod = getAsyncMethod(poll, invokeExpr,u);
                                if (asyncMethod != null) {
                                    for (SootMethod method : asyncMethod.keySet()) {
                                        if (method == null)
                                            continue;
                                        targetMethods.add(method);
                                        kind = asyncMethod.get(method);
                                    }
                                }
                            } else if (name.equals("setOnClickListener")) {
                                //Processing callback
                                Value arg = invokeExpr.getArg(0);
                                Type listener = arg.getType();
                                SootClass listenerClass = Scene.v().getSootClass(listener.toString());

                                SootMethod onClick = findMethod(listenerClass, "void onClick(android.view.View)");
                                if (onClick != null) {
                                    Class<Kind> kindClass = Kind.class;
                                    try {
                                        Constructor<Kind> constructors = kindClass.getDeclaredConstructor(String.class);
                                        constructors.setAccessible(true);
                                        kind = constructors.newInstance("CALLBACK");
                                        targetMethods.add(onClick);
                                    } catch (Exception e) {
                                        e.printStackTrace();
                                    }
                                }
                            } else if (invokeExpr.getMethod().getSignature().equals("<android.content.ContentResolver: android.os.Bundle call(android.net.Uri,java.lang.String,java.lang.String,android.os.Bundle)>")) {
                                //Processing the mapping of call to the actual call method
                                SootMethod method = getCallToRealCallMethod(poll, invokeExpr);
                                if (method != null) {
                                    Class<Kind> kindClass = Kind.class;
                                    try {
                                        Constructor<Kind> constructors = kindClass.getDeclaredConstructor(String.class);
                                        constructors.setAccessible(true);
                                        kind = constructors.newInstance("SYSTEM_CALL");
                                        targetMethods.add(method);
                                    } catch (Exception e) {
                                        e.printStackTrace();
                                    }
                                }
                            } else if (invokeExpr.getMethod().getSignature().equals("<android.os.Handler: boolean sendMessage(android.os.Message)>")) {
                                //Procesing handler
                                logger.info("find handler init site");
                                if(1==1)
                                    continue;
                                HashSet<Unit> handlerNewSiteSet = getNewSite(u, ((InstanceInvokeExpr)invokeExpr).getBase(),poll);
                                if(handlerNewSiteSet.isEmpty()){
                                    logger.info("Can't find handler init site!");
                                    continue;
                                }
                                for(Unit handlerNewSite:handlerNewSiteSet) {
                                    SootClass handler;
                                    if(handlerNewSite instanceof IdentityStmt) {
                                        IdentityStmt identityStmt = (IdentityStmt) handlerNewSite;
                                        ThisRef rightOp = (ThisRef) identityStmt.getRightOp();
                                        handler=Scene.v().getSootClass(rightOp.getType().toString());

                                    }else {
                                        Value rightOp = ((AssignStmt) handlerNewSite).getRightOp();
                                        NewExpr newExpr = (NewExpr) rightOp;
                                        handler = Scene.v().getSootClass(newExpr.getType().toString());
                                    }
                                    SootMethod handleMessage = findMethod(handler,"void handleMessage(android.os.Message)");
                                    if(handleMessage==null)
                                        continue;
                                    targetMethods.add(handleMessage);
                                    kind = Kind.HANDLER;
                                }
                            }else if(invokeExpr.getMethod().getSignature().equals("<android.view.View: void invalidate()>")){
                                //Process refresh calls in the system
                                VirtualInvokeExpr virtualInvokeExpr = (VirtualInvokeExpr) invokeExpr;
                                String baseClsName = virtualInvokeExpr.getBase().getType().toString();
                                SootClass baseCls = Scene.v().getSootClass(baseClsName);
                                SootMethod method = findMethod(baseCls, "void onDraw(android.graphics.Canvas)");
                                if (method != null) {
                                    Class<Kind> kindClass = Kind.class;
                                    try {
                                        Constructor<Kind> constructors = kindClass.getDeclaredConstructor(String.class);
                                        constructors.setAccessible(true);
                                        kind = constructors.newInstance("SYSTEM_CALL");
                                        targetMethods.add(method);
                                    } catch (Exception e) {
                                        e.printStackTrace();
                                    }
                                }
                            }else {
                                if (invokeExpr instanceof VirtualInvokeExpr) {
                                    //The refresh call to virtual in the processing system corresponds to the instance method, 
                                    // which is the related method implemented in the subclass, or if the method is implemented in this class, 
                                    // the method in this class is also added
                                    HashSet<SootMethod> methods = dispatchAbstract(sootClass, invokeExpr.getMethod());
                                    if (!methods.isEmpty()) {
                                        targetMethods.addAll(methods);
                                        kind = Kind.VIRTUAL;
                                    }
                                } else {
                                    //For interface calls, we only focus on which user-defined interfaces, 
                                    // and for some interfaces provided by java, we don't look for ways to actually implement the relevant interfaces
                                    if (isSystemClass(sootClass.getName())&&!isUserKeepClass(sootClass.getName())) {
                                        targetMethods.add(invokeExpr.getMethod());
                                    } else {
                                        targetMethods.addAll(dispatchAbstract(sootClass, invokeExpr.getMethod()));
                                        if(isUserKeepClass(sootClass.getName()))
                                            targetMethods.add(invokeExpr.getMethod());
                                    }
                                    kind = Kind.INTERFACE;

                                }
                            }
                        }
                    }

                    for (SootMethod target : targetMethods) {
                        Edge edge = new Edge(poll, u, target, kind);
                        cg.addEdge(edge);
                    }
                    worklist.addAll(targetMethods);
                }
            } catch (Exception e) {
                e.printStackTrace();
            }
        }
        //Update Call Graph
        //Update ReachableMethod
        ReachableMethods reachableMethods = new ReachableMethods(cg, entrypoints);
        Scene.v().setReachableMethods(reachableMethods);
        Scene.v().setCallGraph(cg);
        cg=null;
    }


    public static SootMethod getCallToRealCallMethod(SootMethod method, InvokeExpr invokeExpr) {
        //For call processing, we default to calling the call method that overrides itself for call
        SootClass declaringClass = method.getDeclaringClass();
        return declaringClass.getMethodUnsafe("android.os.Bundle call(java.lang.String,java.lang.String,android.os.Bundle)");
    }

    public static HashMap<SootMethod, Kind> getAsyncMethod(SootMethod method, InvokeExpr invokeExpr,Unit callSite) {
        /*
        The first step in handling asynchrony is to determine the type of instance
         */
        HashMap<SootMethod, Kind> res = new HashMap<>();
        SootMethod apiMethod = invokeExpr.getMethod();
        String apiName = apiMethod.getName();
        String apiSig = apiMethod.getSignature();
        Value value = invokeExpr.getUseBoxes().get(invokeExpr.getUseBoxes().size() - 1).getValue();
        Type type = value.getType();
        SootClass sc = Scene.v().getSootClass(type.toString());
        if (apiSig.equals("<java.lang.Thread: void start()>")) {
            //1、Thread.start form to start, there are two cases, one is inherited from Thead class, the implementation of runnable interface
            //2、Simply pass a Runnable object directly into the initialization of Thread
            if (sc.getName().equals("java.lang.Thread")) {
                for (Unit u : method.retrieveActiveBody().getUnits()) {
                    if (u instanceof InvokeStmt) {
                        InvokeExpr invokeExpr1 = ((InvokeStmt) u).getInvokeExpr();
                        if (invokeExpr1.getMethod().getName().equals("<init>") && invokeExpr1.getUseBoxes().get(invokeExpr1.getUseBoxes().size() - 1).getValue().equals(value)) {
                            Value runArg = invokeExpr1.getArg(0);
                            HashSet<Unit> newSite = getNewSite(callSite, runArg, method);
                            for(Unit uu:newSite){
                                SootClass cls;
                                if( uu instanceof IdentityStmt){
                                    String clsName = ((ThisRef) ((IdentityStmt) uu).getRightOp()).getType().toString();
                                    cls = Scene.v().getSootClass(clsName);
                                }else {
                                    Value rightOp = ((AssignStmt) uu).getRightOp();
                                    NewExpr newExpr = (NewExpr) rightOp;
                                    cls = Scene.v().getSootClass(newExpr.getType().toString());
                                }
                                SootMethod run = findMethod(cls, "void run()");
                                if (run != null) {
                                    res.put(run, Kind.THREAD);
                                }
                            }
                            return res;
                        }
                    }
                }
            } else {
                SootClass threadClass = Scene.v().getSootClass("java.lang.Thread");
                if (isSubClass(sc, threadClass)) {
                    SootMethod run = findMethod(sc, "void run()");
                    if (run == null)
                        return null;
                    res.put(run, Kind.THREAD);
                    return res;
                }
            }
        } else if (apiName.equals("run") && isImplementInterface(sc,"java.lang.Runnable")) {
            //If the Runnable interface is implemented
            SootMethod run = sc.getMethodByNameUnsafe("run");
            if (run == null)
                return null;
            res.put(run, Kind.THREAD);
        }else if((apiName.equals("postDelayed")||apiName.equals("post"))&&isOrSubClass(sc,"android.os.Handler")){
            //Get the Runnable interface
            Value runArg = invokeExpr.getArg(0);
            HashSet<Unit> newSite = getNewSite(callSite, runArg, method);
            for(Unit u:newSite){
                SootClass cls;
                if( u instanceof IdentityStmt){
                    String clsName = ((ThisRef) ((IdentityStmt) u).getRightOp()).getType().toString();
                    cls = Scene.v().getSootClass(clsName);
                }else {
                    Value rightOp = ((AssignStmt) u).getRightOp();
                    NewExpr newExpr = (NewExpr) rightOp;
                    cls = Scene.v().getSootClass(newExpr.getType().toString());
                }
                SootMethod run = findMethod(cls,"void run()");
                if(run!=null){
                    res.put(run,Kind.THREAD);
                }
            }
            return res;
        } else if (apiName.equals("execute") && isOrSubClass(sc,"android.os.AsyncTask")&&!sc.getName().equals("android.os.AsyncTask")) {
            for (SootMethod m : sc.getMethods()) {
                if (m.getName().equals("doInBackground")) {
                    boolean flag = true;
                    for (Unit uu : m.retrieveActiveBody().getUnits())
                        if (uu.toString().contains("doInBackground")) {
                            flag = false;
                            break;
                        }
                    if (flag) {
                        res.put(m, Kind.ASYNCTASK);
                        return res;
                    }
                }

            }
        } else if (apiName.equals("execute") && (isImplementInterface(sc,"java.util.concurrent.Executor")||isOrSubClass(sc,"java.util.concurrent.Executor"))) {
            //The execute parameter is the thread to execute
            Value runArg = invokeExpr.getArg(0);
            HashSet<Unit> newSite = getNewSite(callSite, runArg, method);
            for(Unit u:newSite){
                SootClass cls;
                if( u instanceof IdentityStmt){
                    String clsName = ((ThisRef) ((IdentityStmt) u).getRightOp()).getType().toString();
                    cls = Scene.v().getSootClass(clsName);
                }else {
                    Value rightOp = ((AssignStmt) u).getRightOp();
                    NewExpr newExpr = (NewExpr) rightOp;
                    cls = Scene.v().getSootClass(newExpr.getType().toString());
                }
                SootMethod run = findMethod(cls,"void run()");
                if(run!=null){
                    res.put(run,Kind.EXECUTOR);
                }
            }
            return res;
        }
        return null;
    }


    public static boolean isVisible(SootMethod m, SootClass cls) {
        FastHierarchy hierarchy = Scene.v().getOrMakeFastHierarchy();
        if (m.isPublic()) {
            return true;
        } else if (m.isPrivate()) {
            return m.getDeclaringClass().getName().equals(cls.getName());
        } else {
            return m.isProtected() ? hierarchy.canStoreClass(cls, m.getDeclaringClass()) : cls.getJavaPackageName().equals(m.getDeclaringClass().getJavaPackageName());
        }
    }


    public static SootMethod dispatchConcrete(SootClass cls, SootMethod method) {
        String subSignature = method.getSubSignature();
        SootClass temp = cls;
        do {
            SootMethod m = cls.getMethodUnsafe(subSignature);
            if (m != null) {
                if ((m.isConcrete() && isVisible(method, temp)) || isSystemClass(cls.getName())) {
                    return m;
                } else {
                    return null;
                }
            }
            cls = cls.getSuperclassUnsafe();
        } while (cls != null);
        return null;
    }

    public static boolean isCustomizedEndpoint(SootMethod method){
        if(customizedEndpoints.contains(method.getSignature()))
            return true;
        return false;
    }

    public static void setCustomizedEndpoint(String endpoint){
        customizedEndpoints.add(endpoint);
    }

    //
    public static HashSet<SootMethod> dispatchAbstract(SootClass cls, SootMethod method) {
        HashSet<SootMethod> targetMethod = new HashSet<>();

        //Allows customized Interface analysis of the interface
        if(isCustomizedEndpoint(method)){
            targetMethod.add(method);
            return targetMethod;
        }

        Queue<SootClass> worklist = new LinkedList<>();
        worklist.add(cls);
        FastHierarchy hierarchy = Scene.v().getOrMakeFastHierarchy();
        while (!worklist.isEmpty()) {
            SootClass currentClass = worklist.poll();
            if (currentClass == null)
                continue;
            if (currentClass.isInterface()) {
                worklist.addAll(hierarchy.getAllImplementersOfInterface(currentClass));
            } else {
                SootMethod m = dispatchConcrete(currentClass, method);
                if (m != null)
                    targetMethod.add(m);
                Collection<SootClass> subclassesOf = hierarchy.getSubclassesOf(currentClass);
                worklist.addAll(subclassesOf);
            }
        }
        return targetMethod;
    }

    public static HashSet<SootMethod> getMethod(Unit u) {
        HashSet<SootMethod> res = new HashSet<>();
        InvokeExpr invokeExpr = null;
        if (u instanceof InvokeStmt) {
            InvokeStmt invokeStmt = (InvokeStmt) u;
            invokeExpr = invokeStmt.getInvokeExpr();
        }

        if (u instanceof AssignStmt) {
            AssignStmt assignStmt = (AssignStmt) u;
            if (assignStmt.containsInvokeExpr())
                invokeExpr = assignStmt.getInvokeExpr();
        }
        if (invokeExpr == null)
            return res;
        if (invokeExpr instanceof StaticInvokeExpr) {
            res.add(invokeExpr.getMethod());
        } else {
            int size = invokeExpr.getUseBoxes().size();
            Type type = invokeExpr.getUseBoxes().get(size - 1).getValue().getType();
            SootClass cls = Scene.v().getSootClass(type.toString());

            if (invokeExpr instanceof SpecialInvokeExpr) {
                SootMethod method = dispatchConcrete(cls, invokeExpr.getMethod());
                if (method != null)
                    res.add(method);
            }

            if ((invokeExpr instanceof InterfaceInvokeExpr) || (invokeExpr instanceof VirtualInvokeExpr)) {
                res.addAll(dispatchAbstract(cls, invokeExpr.getMethod()));
            }
        }
        return res;
    }

    public static boolean isSubClass(SootClass child, SootClass fatherClass) {
        SootClass superclass = child.getSuperclass();
        while (!(superclass.getName().equals(fatherClass.getName()) || superclass.getName().equals("java.lang.Object"))) {
            superclass = superclass.getSuperclass();
        }
        return !superclass.getName().equals("java.lang.Object");
    }

    public static boolean isImplementInterface(SootClass cls,String interfaceName){
        if(cls.implementsInterface(interfaceName))
            return true;
        if(!cls.hasSuperclass())
            return false;
        return isImplementInterface(cls.getSuperclass(),interfaceName);
    }

    public static boolean isOrSubClass(SootClass curCls,String targetCls){
        if(curCls.getName().equals(targetCls))
            return true;
        if(curCls.hasSuperclass()){
            return isOrSubClass(curCls.getSuperclass(),targetCls);
        }else {
            return false;
        }
    }


    public static boolean isUserKeepClass(String clsName){
        // Define some of the methods that users need to track
        if(clsName.equals("android.content.SharedPreferences"))
            return true;
        return false;
    }

    public static boolean isThirdPartyLibrary(String clsName){
        if(clsName.startsWith("com.facebook."))
            return true;
        return false;

    }
    public static void insertCallBackInCallGraph() {
        if (!Scene.v().hasCallGraph()) {
            throw new RuntimeException("No Call graph!");
        }


    }

    public static SootMethod findMethod(SootClass cls, String subsignature) {
        if (cls == null)
            return null;
        SootMethod method = cls.getMethodUnsafe(subsignature);
        if (method != null)
            return method;
        if (!cls.hasSuperclass())
            return null;
        return findMethod(cls.getSuperclass(), subsignature);
    }

    public static HashSet<SootMethod> getAllMethodsCanReachTargetMethods(HashSet<SootMethod> targetMethods) {
        //Find all the ways to reach the target method
        HashSet<SootMethod> reachableMethods=new HashSet<>();
        for(SootMethod targetMethod:targetMethods){
            getReachableMethodInDepth(reachableMethods,targetMethod,0);
        }
        logger.info("[Reachable Method Size]: {}",reachableMethods.size());
        return reachableMethods;
    }

    public static void getAllPathsTotTargetMethod(SootMethod targetMethod,SootMethod curMethod,int depth,List<String> path){
        //Find all reachable methods and print them out
        if(curMethod.equals(targetMethod)){
            path.add(targetMethod.getSignature());
            logger.info(path.toString());

            try{
                FileWriter fileWriter = new FileWriter("./path_info.txt", true);
                BufferedWriter writer = new BufferedWriter(fileWriter);
                writer.write("path info:\n");
                int counter=0;
                for(String m:path){
                    writer.write("["+counter+"]: "+m+"\n");
                    counter++;
                }
                writer.close();

            }catch (Exception e){
                e.printStackTrace();
            }
            path.remove(path.size()-1);
            return;
        }
        //Avoid loops
        if(path.contains(curMethod.getSignature())){
            return;
        }
        //Over maximum depth
        if(depth>10){
            return;
        }

        CallGraph cg = Scene.v().getCallGraph();
        Iterator<Edge> edgeIterator = cg.edgesOutOf(curMethod);
        path.add(curMethod.getSignature());
        while (edgeIterator.hasNext()){
            SootMethod tgt = edgeIterator.next().tgt();
            getAllPathsTotTargetMethod(targetMethod,tgt,depth+1,path);
        }
        path.remove(curMethod.getSignature());
    }

    //Find the place where a variable was initialized
    public static HashSet<Unit> getNewSite(Unit unit, Value value, SootMethod curMethod) {
        HashSet<Unit> res=new HashSet<>();

        HashSet<Trace> traces=new HashSet<>();
        Queue<Trace> queue=new LinkedList<>();
        
        queue.add(new Trace(unit,curMethod,value));
        while (!queue.isEmpty()){
            Trace curTrace = queue.poll();
            traces.add(curTrace);
    
            HashSet<Unit> allDirectUnit = getAllDirectUnit(curTrace.v, curTrace.u, curTrace.m);
            for(Unit defUnit:allDirectUnit){
                if(defUnit instanceof AssignStmt){
                    AssignStmt assignStmt = (AssignStmt) defUnit;
                    Value rightOP = assignStmt.getRightOp();
                    if(rightOP instanceof NewExpr){
                        res.add(defUnit);
                        continue;
                    }
                    
                    if(rightOP instanceof InvokeExpr){
                        SootMethod method = ((InvokeExpr) rightOP).getMethod();
                        if(method.isConcrete()){
                            BriefUnitGraph graph = new BriefUnitGraph(method.retrieveActiveBody());
                            for(Unit tail:graph.getTails()){
                                if(tail instanceof ReturnStmt){
                                    ReturnStmt returnStmt = (ReturnStmt) tail;
                                    Value op = returnStmt.getOp();
                                    if(op instanceof NullConstant)
                                        continue;
                                    Trace trace = new Trace(tail, method, op);
                                    if(!traces.contains(trace)){
                                        queue.add(trace);
                                    }
                                }
                            }
                        }

                    }else if(rightOP instanceof Local){
                        
                        Trace trace = new Trace(defUnit, curTrace.m, rightOP);
                        if(!traces.contains(trace)){
                            queue.add(trace);
                        }
                    }else if(rightOP instanceof InstanceFieldRef){
                        
                        SootClass declaringClass = curTrace.m.getDeclaringClass();
                        
                        InstanceFieldRef instanceFieldRef = (InstanceFieldRef) rightOP;
                        for(SootMethod m:declaringClass.getMethods()){
                            if(!m.isConcrete())
                                continue;
                            for(Unit u:m.retrieveActiveBody().getUnits()){
                                if(u instanceof AssignStmt){
                                    AssignStmt assignOp= (AssignStmt) u;
                                    Value assignOpLeftOp = assignOp.getLeftOp();
                                    if(assignOpLeftOp instanceof InstanceFieldRef){
                                        InstanceFieldRef filedRef = (InstanceFieldRef) assignOpLeftOp;
                                        if(filedRef.getField().equals(instanceFieldRef.getField())){
                                            
                                            Value rightOp = assignOp.getRightOp();
                                            
                                            if(rightOp instanceof NullConstant)
                                                continue;
                                            
                                            Trace trace = new Trace(u, m, rightOp);
                                            if(!traces.contains(trace)){
                                                queue.add(trace);
                                            }
                                        }
                                    }

                                }
                            }
                        }

                    }else if(rightOP instanceof StaticFieldRef){
                        
                        SootClass declaringClass = curTrace.m.getDeclaringClass();
                        for(SootMethod m:declaringClass.getMethods()){
                            if(!m.isConcrete())
                                continue;
                            for(Unit u:m.retrieveActiveBody().getUnits()){
                                if(u instanceof AssignStmt){
                                    AssignStmt assignOp = (AssignStmt) u;
                                    Value leftOp = assignOp.getLeftOp();
                                    if(leftOp.equals(rightOP)){
                                        
                                        Value rightOp = assignOp.getRightOp();
                                        
                                        if(rightOp instanceof NullConstant)
                                            continue;
                                        Trace trace = new Trace(u, m, rightOp);
                                        if(!traces.contains(trace))
                                            queue.add(trace);

                                    }
                                }
                            }
                        }
                    }
                }else {
                    //Track parameter
                    Iterator<Edge> callers = cg.edgesInto(curTrace.m);
                    IdentityStmt identityStmt = (IdentityStmt) defUnit;
                    Value rightOp = identityStmt.getRightOp();
                    if(rightOp instanceof ThisRef) {
                        res.add(defUnit);
                        continue;
                    }
                    ParameterRef pr = (ParameterRef) rightOp;
                    
                    int index = pr.getIndex();
                    while (callers.hasNext()){
                        Edge next = callers.next();
                        SootMethod src = next.src();
                        Unit callSite = next.srcUnit();
                        
                        InvokeExpr invokeExpr = getInvokeExpr(callSite);
                        if(invokeExpr==null){
                            logger.warn("Error:{} is not a call Site!",callSite.toString());
                            continue;
                        }
                        Value v = invokeExpr.getArg(index);
                        Trace trace = new Trace(callSite, src, v);
                        if(!traces.contains(trace))
                            queue.add(trace);
                    }

                }
            }
        }
        return res;
    }

    public static HashSet<Unit> getAllDirectUnit(Value value,Unit curUnit,SootMethod method){
        //Finds all direct assignment statements for the specified variable
        HashSet<Unit> res=new HashSet<>();
        BriefUnitGraph graph = new BriefUnitGraph(method.retrieveActiveBody());
        Queue<Unit> queue=new LinkedList<>();
        queue.add(curUnit);
        HashSet<Unit> visited=new HashSet<>();
        while (!queue.isEmpty()){
            Unit poll = queue.poll();
            visited.add(poll);
            for(Unit preUnit:graph.getPredsOf(poll)){
                if(visited.contains(preUnit))
                    continue;
                if(isValueDefinedInUnit(preUnit,value)){
                    res.add(preUnit);
                    continue;
                }
                queue.add(preUnit);
            }
        }
        return res;
    }

    public static Unit getDirectDefUnit(Unit curUnit, Value value, SootMethod method) {
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

    public static boolean isValueDefinedInUnit(Unit unit, Value value) {
        //Determines whether value is defined in the current statement
        if(unit instanceof AssignStmt){
            AssignStmt assignStmt = (AssignStmt) unit;
            return assignStmt.getLeftOp().equals(value);
        }

        if(unit instanceof IdentityStmt){
            IdentityStmt identityStmt = (IdentityStmt) unit;
            return identityStmt.getLeftOp().equals(value);
        }
        return false;
    }


    static class Trace{
        Unit u;
        SootMethod m;
        Value v;

        public Trace(Unit u,SootMethod m,Value v){
            this.m=m;
            this.u=u;
            this.v=v;
        }

        @Override
        public boolean equals(Object obj) {
            if(!(obj instanceof Trace))
                return false;
            Trace trace = (Trace) obj;
            return this.v.equals(trace.v)&&this.m.equals(trace.m)&&this.u.equals(trace.u);
        }

        @Override
        public int hashCode() {
            return Objects.hash(m,u,v);
        }

        @Override
        public String toString() {
            return "[Unit]:"+u+'\n'+
                    "[Method]:"+m.getSignature()+'\n'+
                    "[Value]:"+v;
        }
    }

    public static void getPath(SootMethod curMethod,SootMethod targetMethod,List<SootMethod> path,int depth){
        if(depth>40) {
            return;
        }
        if(curMethod.equals(targetMethod)){
            showPath(path);
            return;
        }
        CallGraph callGraph = Scene.v().getCallGraph();
        Iterator<Edge> edgeIterator = callGraph.edgesInto(curMethod);
        while (edgeIterator.hasNext()){
            Edge next = edgeIterator.next();
            SootMethod src = next.src();
            if(path.contains(src))
                continue;
            List<SootMethod> newPath=new ArrayList<>(path);
            newPath.add(curMethod);
            getPath(src,targetMethod,newPath,depth+1);
        }
    }

    public static void showPath(List<SootMethod> path){
        Collections.reverse(path);
        logger.info(path.toString());
    }


    public static void getReachableMethodInDepth(HashSet<SootMethod> reachableMethods,SootMethod curMethod,int depth){
        //Find the reachability method for the specified depth
        if(depth>10)
            return;
        CallGraph callGraph = Scene.v().getCallGraph();
        reachableMethods.add(curMethod);
        Iterator<Edge> edgeIterator = callGraph.edgesInto(curMethod);
        while (edgeIterator.hasNext()){
            SootMethod src = edgeIterator.next().src();
            if(reachableMethods.contains(src))
                continue;
            getReachableMethodInDepth(reachableMethods,src,depth+1);
        }
    }

    public static void getPathBackWard(Unit curUnit, Unit beginUnit, int depth, List<List<Unit>> res, DirectedGraph<Unit> graph,List<Unit> path){
        if(depth>20)
            return;
        if(curUnit.equals(beginUnit)){
            res.add(path);
        }
        for(Unit preUnit:graph.getPredsOf(curUnit)){
            if(path.contains(preUnit))
                continue;
            List<Unit> newPath=new ArrayList<>(path);
            newPath.add(preUnit);
            getPathBackWard(preUnit,beginUnit,depth+1,res,graph,newPath);
        }
    }

    public static void getReachableMethodInGivenSet(SootMethod curMethod,HashSet<SootMethod> givenMethods,int depth,List<List<String>> paths,List<String> path){
        if(depth>5)
            return;
        if(givenMethods.contains(curMethod)) {
            paths.add(path);
        }
        CallGraph callGraph = Scene.v().getCallGraph();
        Iterator<Edge> edgeIterator = callGraph.edgesOutOf(curMethod);
        while (edgeIterator.hasNext()){
            SootMethod tgt = edgeIterator.next().tgt();
            List<String> newPath=new ArrayList<>(path);
            newPath.add(tgt.getSignature());
            getReachableMethodInGivenSet(tgt,givenMethods,depth+1,paths,newPath);
        }
    }

    public static void getReachableMethodInGivenSet(SootMethod curMethod,HashSet<SootMethod> givenMethods,int depth,List<String> res,HashSet<SootMethod> visited){
        if(depth>5)
            return;
        if(visited.contains(curMethod))
            return;
        visited.add(curMethod);
        if(givenMethods.contains(curMethod))
            res.add(curMethod.getSignature());
        CallGraph callGraph = Scene.v().getCallGraph();
        Iterator<Edge> edgeIterator = callGraph.edgesOutOf(curMethod);
        while (edgeIterator.hasNext()){
            SootMethod tgt = edgeIterator.next().tgt();
            getReachableMethodInGivenSet(tgt,givenMethods,depth+1,res,visited);
        }

    }


    public static InvokeExpr getInvokeExpr(Unit u){
        if(u instanceof AssignStmt){
            AssignStmt assignStmt = (AssignStmt) u;
            if(assignStmt.containsInvokeExpr())
                return assignStmt.getInvokeExpr();
        }
        if(u instanceof InvokeStmt){
            InvokeStmt invokeStmt = (InvokeStmt) u;
            return invokeStmt.getInvokeExpr();
        }

        return null;

    }


    public static Set<String> getAllFields(SootClass sootClass){ //The Field name is class.name #FieldName
        Set<String> fields = new HashSet<>();

        // Iterate over the fields of the current class
        for (SootField field : sootClass.getFields()) {
            fields.add(sootClass.getName() +"#"+ field.getName());
        }

        // Iterate over the inner classes of the current class
        for (SootClass innerClass : Scene.v().getClasses()) {
            if (isInnerClass(innerClass, sootClass.getName())) {
                fields.addAll(getAllFields(innerClass));
            }
        }

        return fields;
    }

    public static boolean isInnerClass(SootClass innerClass, String outerClassName) {
        String innerClassName = innerClass.getName();
        return innerClassName.startsWith(outerClassName + "$");
    }


}
