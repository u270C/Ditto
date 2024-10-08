package dataflow;

import cg.CallGraphUtils;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.*;
import soot.jimple.*;
import soot.jimple.toolkits.callgraph.Edge;
import soot.toolkits.graph.BriefUnitGraph;

import java.util.*;

/**
 * @program: Ditto
 * @description: Basic functions for data flow engine
 **/
public abstract class AbstractDataFlow implements Analyze {

    public static final Logger logger = LoggerFactory.getLogger(AbstractDataFlow.class);

    protected int MAX_DEPTH = 15;

    protected Analyze analyze = null;

    public void run() {

    }

    public void setMAX_DEPTH(int depth){
        this.MAX_DEPTH=depth;
    }

    public static boolean isValueUsedInUnit(Unit unit, Value value) {
        List<String> usedValue = new ArrayList<>();
        for (ValueBox useBox : unit.getUseBoxes()) {
            usedValue.add(useBox.getValue().toString());
        }
        return usedValue.contains(value.toString());
    }

    public static boolean isValueDefinedInUnit(Unit unit, Value value) {
        List<String> definedValue = new ArrayList<>();
        for (ValueBox defBox : unit.getDefBoxes()) {
            definedValue.add(defBox.getValue().toString());
        }
        return definedValue.contains(value.toString());
    }


    public static Unit getParmaAssignUnit(BriefUnitGraph graph, int paramIndex) {
        Queue<Unit> queue = new LinkedList<>(graph.getHeads());
        HashSet<Unit> visit = new HashSet<>();
        while (!queue.isEmpty()) {
            Unit poll = queue.poll();
            visit.add(poll);
            if (poll.toString().contains("@parameter" + paramIndex)) {
                return poll;
            }
            for (Unit succor : graph.getSuccsOf(poll)) {
                if (!visit.contains(succor))
                    queue.add(succor);
            }
        }
        return null;
    }

    public static boolean isSystemClass(SootClass sootClass) {
        String name = sootClass.getName();
        if (name.startsWith("java") || name.startsWith("javax")||name.startsWith("android.")||name.startsWith("androidx.")||name.startsWith("com.android")||name.startsWith("sun.")) {
            return true;
        }
//
//        if(name.startsWith("java.")||name.startsWith("javax."))
//            return true;
        return false;

    }

    public static boolean isSystemClassName(String name) {
        if (name.startsWith("java") || name.startsWith("javax")||name.startsWith("android.")||name.startsWith("androidx.")||name.startsWith("com.android")||name.startsWith("sun.")) {
            return true;
        }else if(name.equals("boolean")||name.equals("int")||name.equals("char")||name.equals("byte"))
            return true;
        return false;

    }


    public static boolean isMethodCalled(List<CallSite> callStack, SootMethod method) {
        for (CallSite callSite : callStack) {
            if (callSite.caller!=null && callSite.caller.getSignature().equals(method.getSignature()))
                return true;
        }
        return false;
    }


    //Find a direct assignment statement for a variable
    public Unit findDirectDefUnit(ValueBox valueBox, Unit u, SootMethod m) {
        if (!m.isConcrete())
            return null;
        BriefUnitGraph cfg = new BriefUnitGraph(m.retrieveActiveBody());
        Queue<Unit> queue = new LinkedList<>();
        queue.addAll(cfg.getPredsOf(u));
        HashSet<Unit> visit = new HashSet<>();
        while (!queue.isEmpty()) {
            Unit poll = queue.poll();
            visit.add(poll);
            if (isValueDefinedInUnit(poll, valueBox.getValue())) {
                return poll;
            }
            for (Unit pre : cfg.getPredsOf(poll)) {
                if (!visit.contains(pre))
                    queue.add(pre);
            }
        }
        return null;
    }

    public static InvokeExpr getInvokeExpr(Unit u){

        if(u instanceof InvokeStmt){
            return ((InvokeStmt)u).getInvokeExpr();
        }

        if(u instanceof AssignStmt){
            AssignStmt assignStmt = (AssignStmt) u;
            if(assignStmt.containsInvokeExpr())
                return assignStmt.getInvokeExpr();
        }
        return null;
    }

    public static HashSet<SootMethod> getMethodFromCG(Unit u) {
        return CallGraphUtils.getMethod(u);
    }







}
