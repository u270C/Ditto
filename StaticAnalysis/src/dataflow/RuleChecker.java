package dataflow;

import soot.SootMethod;
import soot.Unit;
import soot.ValueBox;

/**
 * @program: Ditto
 * @description: The rule checks the interface to determine whether the data flow reaches the sink point in this method
 **/
public interface RuleChecker {
    //Determines whether a data flow such as to a call is a sink
    boolean isSink(Unit checkedUnit, ValueBox taintValueBox);

    //Determine whether an invocation that depends on the control flow is a sink
    boolean isDependConditionSink(SootMethod method,SootMethod caller);
}
