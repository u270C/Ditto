package dataflow;

import soot.SootMethod;
import soot.Unit;

import java.util.Objects;

/**
 * @program: Ditto
 * @description:
 **/
public class CallSite {
    public SootMethod caller;
    public SootMethod callee;
    public Unit invokeUnit;
    public int paramIndex=-1;

    public CallSite(SootMethod caller, Unit invokeUnit,int paramIndex) {
        this.caller = caller;
        this.invokeUnit = invokeUnit;
        this.paramIndex=paramIndex;
    }

    public CallSite(SootMethod caller, SootMethod callee, Unit invokeUnit, int paramIndex){
        this.caller = caller;
        this.callee = callee;
        this.invokeUnit = invokeUnit;
        this.paramIndex=paramIndex;
    }

    @Override
    public boolean equals(Object obj) {
        if(this==obj)
            return true;
        if(!(obj instanceof CallSite))
            return false;
        CallSite callSite = (CallSite) obj;
        boolean a = (this.caller == null && callSite.caller == null) ||
                (this.caller != null && callSite.caller != null && this.caller.equals(callSite.caller));
        boolean b = (this.invokeUnit!=null && callSite.invokeUnit!=null && this.invokeUnit.toString().equals(callSite.invokeUnit.toString()));
        boolean c = (this.callee == null && callSite.callee == null) ||
                (this.callee != null && callSite.callee != null && this.callee.equals(callSite.callee));
        return a && b && c;
    }


    @Override
    public int hashCode() {
        return Objects.hash(this.caller,this.callee);
    }

    @Override
    public String toString() {
        return "CallSite{" +
                "caller=" + caller +
                ", callee=" + callee +
                ", invokeUnit=" + ((invokeUnit==null)?"null":invokeUnit) +
                '}';
    }
}
