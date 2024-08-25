package analyze;

import WebAPIAnalyzer.APIAnalyzer;
import cg.CallGraphUtils;
import component.EntryPointAnalyze;
import component.ResolveManifest;
import constant.ApkAndJavaConstants;
import constant.EntryPointsDefinition;
import constant.NetworkAPIDefinition;
import constant.StrawPointsDefinition;
import dataflow.Point;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.xmlpull.v1.XmlPullParserException;
import soot.*;
import soot.jimple.AssignStmt;
import soot.jimple.infoflow.android.manifest.ProcessManifest;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import util.DirTraversal;
import util.Log;
import util.SootInit;

import java.io.*;
import java.lang.reflect.Array;
import java.util.*;


/**
 * @program: Ditto
 * @description: The main function that receives and processes the target apk file.
 **/
public class Main {

    public static final Logger logger = LoggerFactory.getLogger(Main.class);

    public static  String apkDir=System.getProperty("user.dir")+ File.separator+"app";

    public static String androidJar=ApkAndJavaConstants.androidJarPath+File.separator+"android.jar";

    public static  String logFileName="RuntimeLog";

    public static  String filterAppInfo="./appFinished.txt";

    public static String dataSavedDir=System.getProperty("user.dir")+File.separator+"analyze_result";

    public static void main(String[] args) throws IOException, XmlPullParserException {

        Log.openLog(logFileName, false);

        String apkPath = args[1];

        run(apkPath);

        Log.closeLog();

    }

    public static void run(String apkPath){

        File apkFile = new File(apkPath);

        Log.write(Log.Mode.APP, apkFile.getName());
        String versionName = ResolveManifest.getVersionName(apkFile);
        Log.write(Log.Mode.VERSION,versionName);
        Log.write(Log.Mode.PATH,apkFile.getPath());

        logger.info("Static analysis for {}", apkFile.getName());

        // Initiate Soot program
        SootInit.initSootForAndroid(apkPath, androidJar);

        // Find entrypoints of apk
        HashSet<SootMethod> entrypoints = EntryPointAnalyze.getEventHandlerMethodByComponent();
        // Find the network library methods used possibly in the program.
        ArrayList<String> pois = NetworkAPIDefinition.getPOIList();
        CallGraphUtils.buildCGbyCHA(new ArrayList<>(entrypoints));
        // Start API functions analysis, whether they are DUSS-related.
        APIAnalyzer analyzer = new APIAnalyzer();
        analyzer.analyze(entrypoints,pois);

    }

}
