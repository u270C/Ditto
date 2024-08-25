package component;

import constant.EntryPointsDefinition;
import javafx.scene.Scene;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.*;
import soot.jimple.*;
import soot.jimple.infoflow.InfoflowConfiguration;
import soot.jimple.infoflow.android.InfoflowAndroidConfiguration;
import soot.jimple.infoflow.android.SetupApplication;
import soot.toolkits.graph.BriefUnitGraph;

import java.util.*;


/**
 * @program: Ditto
 * @description: Extract the entrypoints of an Android app, including lifecycle methods and click handlers.
 **/
public class EntryPointAnalyze {

    private static final Logger logger = LoggerFactory.getLogger(EntryPointAnalyze.class);

    public static HashSet<SootMethod> getEventHandlerMethodByComponent() {
        HashSet<SootMethod> res = new HashSet<>();
        for(SootClass sc : Scene.v().getApplicationClasses()){
            if(sc.implementsInterface("android.view.View$OnClickListener")){
                SootMethod onclick= findMethodBySubSignature(sc, "void onClick(android.view.View)");
                if(onclick!=null){
                    logger.info("add entrypoint"+onclick.getSignature());
                    res.add(onclick);
                }
                SootMethod onLongClick = findMethodBySubSignature(sc, "boolean onLongClick(android.view.View)");
                if(onLongClick!=null){
                    logger.info("add entrypoint"+onLongClick.getSignature());
                    res.add(onLongClick);
                }
            }else if (sc.implementsInterface("android.widget.AdapterView$OnItemClickListener")){
                SootMethod onItemClick = findMethodBySubSignature(sc, "void onItemClick(android.widget.AdapterView,android.view.View,int,long)");
                if(onItemClick!=null){
                    logger.info("add entrypoint"+onItemClick.getSignature());
                    res.add(onItemClick);
                }
            }
        }
        if (res.isEmpty()) {
            logger.warn("Can't find the button click");
        } 
        return res;
    }

    private static SootMethod findMethodBySubSignature(SootClass currentClass, String subsignature) {
        if (currentClass.getName().startsWith("android.") || currentClass.getName().startsWith("androidx"))
            return null;

        SootMethod m = currentClass.getMethodUnsafe(subsignature);

        if (m != null) {
            return m;
        }
        if (currentClass.hasSuperclass()) {
            return findMethodBySubSignature(currentClass.getSuperclass(), subsignature);
        }
        return null;
    }

    private static SootMethod findMethodByName(SootClass currentClass, String methodName) {
        if (currentClass.getName().startsWith("android.") || currentClass.getName().startsWith("androidx"))
            return null;

        SootMethod m = currentClass.getMethodByNameUnsafe(methodName);
        if (m != null) {
            return m;
        }
        if (currentClass.hasSuperclass()) {
            return findMethodByName(currentClass.getSuperclass(), methodName);
        }
        return null;
    }

    public static HashSet<SootMethod> getLifeCycleMethodByComponent(String componentName, List<String> lifeCycleMethods) {
        HashSet<SootMethod> res = new HashSet<>();
        SootClass currentClass = Scene.v().getSootClassUnsafe(componentName);
        if (currentClass == null) {
            logger.warn("Can't find the {} class", componentName);
        } else {
            for (String method : lifeCycleMethods) {
                SootMethod lifeCycleMenthod = findMethodBySubSignature(currentClass, method);
                if (lifeCycleMenthod != null)
                    res.add(lifeCycleMenthod);
            }
        }
        return res;
    }


    private static HashSet<SootMethod> getHandlerPublicMethod(String className) {
        HashSet<SootMethod> res = new HashSet<>();
        SootClass handlerClass = Scene.v().getSootClass(className);
        SootMethod onHandleMessage = handlerClass.getMethodByNameUnsafe("handleMessage");
        res.add(onHandleMessage);
        return res;
    }

    private static boolean isValueDefInUnit(Unit unit, Value value) {
        for (ValueBox valueBox : unit.getDefBoxes()) {
            if (valueBox.getValue().toString().equals(value.toString()))
                return true;
        }
        return false;
    }


    public static boolean isSystemClass(String clsName) {
        if (clsName.startsWith("java.") || clsName.startsWith("javax."))
            return true;
        if (clsName.startsWith("android.") || clsName.startsWith("androidx.") || clsName.startsWith("com.google.") || clsName.startsWith("com.android."))
            return true;
        if (clsName.startsWith("jdk"))
            return true;
        if (clsName.startsWith("sun."))
            return true;
        if (clsName.startsWith("org.omg") || clsName.startsWith("org.w3c.dom"))
            return true;
        return false;

    }


    public static HashSet<SootMethod> getClinitMethod(){
        //Gets all static methods of the environment
        HashSet<SootMethod> clinitSet=new HashSet<>();
        for(SootClass cls:Scene.v().getApplicationClasses()){
            if(isSystemClass(cls.getName()))
                continue;
            SootMethod clintMethod = cls.getMethodUnsafe("void <clinit>()");
            if(clintMethod!=null)
                clinitSet.add(clintMethod);
        }
        return clinitSet;
    }


}
