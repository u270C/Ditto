package dataflow;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.SootMethod;

import java.util.HashMap;
import java.util.HashSet;

/**
 * @program: Ditto
 * @description:
 **/
public class TaintWrapper {
    // This class handles wrappers for some basic methods 
 
 
    // Ask to input the corresponding text, according to the rules of the text, to summarize the data flow analysis of some methods 
    // File format 
    // Method name, (Contamination instance, contamination parameter number), return value is contaminated, parameter is contaminated number, instance is contaminated 
    // For example, getIntent,True,_,True,_: indicates that the method needs the instance to be contaminated for its return value to be contaminated


    public static final Logger logger= LoggerFactory.getLogger(TaintWrapper.class);


    class SummeryEffect{
        boolean instanceTaint=false;
        int taintedParamIndex=-1;

        boolean taintRetValue=true;
        int taintParamIndex=-1;
        boolean taintInstance=true;
    }

    HashMap<String,SummeryEffect> methodToEffect=new HashMap<>();




    boolean isInInTaintWrapper(String signature){
        return methodToEffect.containsKey(signature);
    }

    public boolean canAffectRetValue(String signature,boolean instanceTaint,int taintedParamIndex){
        if(!isInInTaintWrapper(signature)) {
            logger.warn("No taint wrapper for the method");
            return false;
        }
        SummeryEffect summeryEffect = methodToEffect.get(signature);
        if(summeryEffect.instanceTaint&&!instanceTaint)
            return false;
        if(summeryEffect.taintedParamIndex!=-1&&taintedParamIndex!= summeryEffect.taintedParamIndex)
            return false;
        return summeryEffect.instanceTaint;


    }

    public boolean canAffectInstance(String signature,int taintedParamIndex){
        if(!isInInTaintWrapper(signature)) {
            logger.warn("No taint wrapper for the method");
            return false;
        }
        SummeryEffect summeryEffect = methodToEffect.get(signature);
        if(summeryEffect.taintedParamIndex!=-1&&taintedParamIndex!= summeryEffect.taintedParamIndex)
            return false;
        return summeryEffect.taintRetValue;
    }

    public int getAffectedParamIndex(String signature,boolean instanceTaint,int taintedParamIndex){
        if(!isInInTaintWrapper(signature)) {
            logger.warn("No taint wrapper for the method");
            return -1;
        }
        SummeryEffect summeryEffect = methodToEffect.get(signature);
        if(summeryEffect.instanceTaint&&!instanceTaint)
            return -1;
        if(summeryEffect.taintedParamIndex!=-1&&taintedParamIndex!= summeryEffect.taintedParamIndex)
            return -1;
        return summeryEffect.taintParamIndex;
    }

    public void setTaintWrapper(String filePath){
        if(filePath==null)
            filePath="";
    }







}
