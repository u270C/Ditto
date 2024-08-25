package WebAPIAnalyzer;

import dataflow.CallSite;
import soot.SootMethod;
import soot.Unit;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

public class Snippet {

    public List<CallSite> callstacks;
    public String strategy = "null";

    public  Snippet(List<CallSite> callstacks){
        this.callstacks = callstacks;
    }

    public void addStrategy(String strategy){
        this.strategy = strategy;
    }

    public SootMethod getPOIMethod(){
        return getAPICallSite().callee;
    }

    public SootMethod getLastCaller(){
        return callstacks.get(callstacks.size()-1).caller;
    }

    public CallSite getAPICallSite(){
        return callstacks.get(callstacks.size()-1);
    }

    public Unit getAPIinvoke(){
        return getAPICallSite().invokeUnit;
    }

    @Override
    public String toString() {
        return callstacks.toString();
    }
}
