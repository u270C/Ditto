package cg;

import soot.SootMethod;
import soot.Unit;
import soot.jimple.toolkits.ide.icfg.JimpleBasedInterproceduralCFG;

import java.util.HashSet;

/**
 * @program: Ditto
 * @description: 
 **/
public class ICFG {


    public HashSet<Unit> getNextUnit(Unit source){
        return null;
    }

    public HashSet<Unit> getCallUnit(Unit returnUnit){
        return null;
    }

    public HashSet<SootMethod> getCalleeMethod(Unit callerUnit){
        return null;
    }

    public void test(){
        JimpleBasedInterproceduralCFG icfg = new JimpleBasedInterproceduralCFG();
        
    }
}
