package dataflow;


import soot.SootMethod;
import soot.Unit;
import soot.ValueBox;

import java.util.HashSet;
import java.util.List;

/**
 * @program: Ditto
 * @description:
 **/
public interface Analyze {

//    boolean flag = false;
    boolean caseAnalyze(Unit unit, SootMethod method, List<CallSite> callStack, HashSet<Point> res, ValueBox taintValueBox);
    boolean returnStatus();
}
