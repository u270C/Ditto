package WebAPIAnalyzer;

import java.util.*;
import java.util.concurrent.ConcurrentLinkedQueue;

import analyze.Main;
import cg.CallGraphUtils;
import constant.NetworkAPIDefinition;
import dataflow.BackwardDataFlow;
import dataflow.CallSite;
import fj.Hash;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.toolkits.callgraph.CallGraph;
import util.Log;

/**
 * @program: Ditto
 * @description:  The main controller of Web API analyzer, suits for different network library strategies, including OKHttp, Java net, Retrofit, GdmOceanNet, and standard Java libraries.
 **/
public class APIAnalyzer {
    private static final Logger logger= LoggerFactory.getLogger(APIAnalyzer.class);
    ArrayList<String> networksigs = NetworkAPIDefinition.getPOIList();
    public Map<String, String> apiURLs = new HashMap<>();
    public Map<String, Unit> jsonModels = new HashMap<>();
    public Set<String> jsonLibraries = new HashSet<>();
    public LinkedList<Snippet> snippets = new LinkedList<Snippet>();
    public Map<CallSite,String> DUSSAPIs = new HashMap<>();

    public APIURLStrategy apiurlStrategy;
    public OkHttpStrategy okHttpStrategy;
    public RetrofitStrategy retrofitStrategy;
    public USSStrategy ussStrategy;
    public GdmStrategy gdmStrategy;

    private MoshiGSONStrategy moshiGsonStrategy;

    public APIAnalyzer(){
        this.apiurlStrategy = new APIURLStrategy(this);
        this.okHttpStrategy = new OkHttpStrategy(this);
        this.moshiGsonStrategy = new MoshiGSONStrategy(this);
        this.retrofitStrategy = new RetrofitStrategy(this,moshiGsonStrategy);
        this.gdmStrategy = new GdmStrategy(this);
    }

    public void analyze(HashSet<SootMethod> entrypoints, ArrayList<String> pois){
        boolean flag = false;
        pois = prunePOI(pois);

        for (SootMethod entryPoint : entrypoints) {
            if (entryPoint == null)
                continue;
            logger.info("begin detecting {}", entryPoint.getSignature());
            Log.write("begin detecting "+ entryPoint.getSignature());
            // Check whether the POI is reachable
            if(reachableAnalyze(entryPoint,pois)) {
                logger.info(entryPoint.getSignature() + " is potential UI event handler");
                Log.write(entryPoint.getSignature() + " is potential UI event handler");
            }
        }
        //Start our Web API analyze
        logger.info("Find "+this.snippets.size()+" snippets");
        Log.write("Find "+this.snippets.size()+" snippets");
        for(Snippet snippet: this.snippets){
            switch (snippet.strategy){
                case "Okhttp":
                    this.okHttpStrategy.extract(snippet);
                    break;
                case "Retrofit":
                    this.retrofitStrategy.extract(snippet);
                    break;
                case "Gdm":
                    this.gdmStrategy.extract(snippet);
                    break;
                default:
                    System.out.println("Unable to find a strategy, thus use default one");
                    this.apiurlStrategy.extract(snippet);
            }
        }
        dumpResult();
    }

    public void dumpResult(){
        logger.info("***Dump result***");
        Log.write("***Dump result***");
        for(CallSite cs : DUSSAPIs.keySet()){
            logger.info("API callsite: "+cs.toString());
            Log.write("API callsite: "+cs.toString());
            logger.info("API Info: "+DUSSAPIs.get(cs));
            Log.write("API Info: "+DUSSAPIs.get(cs));
        }

    }

    private ArrayList<String> prunePOI(ArrayList<String> pois){ // find libraries in current apk
        ArrayList<String> pruned = new ArrayList<String>();
        for(SootClass sc: Scene.v().getClasses()){
            for(String poi : pois){
                String poi_class = poi.substring(poi.indexOf("<")+1,poi.indexOf(":"));
                if(poi_class.equals(sc.getName())) {
                    pruned.add(poi);
                    Log.write("POI: "+poi);
                }
            }
        }
        return pruned;
    }

    private boolean reachableAnalyze(SootMethod method, ArrayList<String> pois) {

        boolean reachable = false;

        logger.info("WebAPIAnalyzer: there are "+pois.size()+" POIs to analyze");
        Log.write("WebAPIAnalyzer: there are "+pois.size()+" POIs to analyze");

        for(String poi : pois){
            HashSet<List<CallSite>> accesspaths = new HashSet<>();
            CallGraph callGraph = Scene.v().getCallGraph();
            if(CallGraphUtils.dfsV2(callGraph,method,poi,15, accesspaths)){
                if(!accesspaths.isEmpty()){
                    logger.info("WebAPIAnalyzer: Total find "+accesspaths.size()+" paths for "+poi);
                    Log.write("WebAPIAnalyzer: Total find "+accesspaths.size()+" paths for "+poi);
                    for(List path : accesspaths){
                        saveSnippet(path,poi);
                    }
                }
                reachable = true;
            }
        }
        return reachable;
    }

    public void saveSnippet(List<CallSite> callstacks, String poi){
        for(int x=0; x<this.snippets.size(); x++){
            Snippet s = this.snippets.get(x);
            CallSite webAPI = s.getAPICallSite();
            if(webAPI.equals(callstacks.get(callstacks.size()-1))){
                if(s.callstacks.size()>callstacks.size()){
                    this.snippets.remove(x);
                    break;
                }
                else return;
            }
        }
        Snippet snippet = new Snippet(callstacks);
        snippet.addStrategy(NetworkAPIDefinition.searchPOIType(poi));
        addSnippet(snippet);
    }

    public void addSnippet(Snippet snippet) {
        this.snippets.add(snippet);
    }

}
