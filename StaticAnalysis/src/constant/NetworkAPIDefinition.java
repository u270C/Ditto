package constant;

import cg.CallGraphUtils;
import org.json.JSONArray;
import org.json.JSONObject;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.tagkit.Tag;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.*;


/**
 * @program: Ditto
 * @description: Analyze the whole program to find the defined network library methods.
 **/
public class NetworkAPIDefinition {

    final public static String NetworkSIGS_FILE = "res/NetworkAPIRequest.txt";
    final public static String NetworkDef_FILE = "res/NetworkAPI.json";
    final public static String NetCallbackSIGS_FILE = "res/networkcallback.txt";
    public static JSONObject POIs = new JSONObject();

    public static HashSet<String> retrofitPOIs = new HashSet<>();

    public static ArrayList<String> getPOIList() {
        getNetworkAPI();
        ArrayList<String> apisigs = new ArrayList<>();

        //For Retrofit API
        for(SootClass sootClass : Scene.v().getApplicationClasses()){
            if(CallGraphUtils.isSystemClass(sootClass.getName())){
                continue;
            }
            for(SootMethod sootMethod : sootClass.getMethods()){
                if(!isretrofitTag(sootMethod) && !isShortURLTag(sootMethod))
                    continue;
                // Check if the API related to URL
                if (sootMethod.getName().toLowerCase().contains("url") || sootMethod.getName().toLowerCase().contains("link")){
                    apisigs.add(sootMethod.getSignature());
                    CallGraphUtils.setCustomizedEndpoint(sootMethod.getSignature());
                    retrofitPOIs.add(sootMethod.getSignature());
                }
            }
        }

        return apisigs;
    }

    public static boolean isShortURLTag(SootMethod sm){
        for(Tag eachtag : sm.getTags()){
            if(eachtag.toString().contains("short") && eachtag.toString().contains("url"))
                return true;
        }
        return false;
    }


    // Find Retrofit API
    public static boolean isretrofitTag(SootMethod sm){
        for(Tag eachtag : sm.getTags()){
            if(eachtag.toString().contains("retrofit"))
                return true;
        }
        return false;
    }

    /**
     * According to the POI function signature, we can determine which type of network library is, 
     * and then we can choose the modeling analysis strategy of the corresponding library
     */
    public static String searchPOIType(String poi){
        String type = "null";
        if(retrofitPOIs.contains(poi))
            return "Retrofit";
        for(String lib:POIs.keySet()){
            JSONObject libobject = POIs.getJSONObject(lib);
            JSONArray featureArray = libobject.getJSONArray("feature");
            JSONArray requestArray = libobject.getJSONArray("request");
            JSONArray responseArray = libobject.getJSONArray("response");
            JSONArray networkmethods = new JSONArray().putAll(featureArray).putAll(requestArray).putAll(responseArray);
            for(Object msig:networkmethods){
                if(msig.toString().equals(poi)){
                    switch (lib){
                        case "GdmOceanNetScene":
                            type = "Gdm";
                            break;
                        case "okhttp3":
                            type = "Okhttp";
                            break;
                        default:
                            type = "APIURL";
                    }
                }
            }
        }
        return type;
    }

    private static List<String> getSignature(String filepath) {
        ArrayList<String> KVsignatures= new ArrayList<>();
        try{
            BufferedReader br = new BufferedReader(new FileReader(filepath));
            String head = br.readLine();
            while(head != null){
                if(!head.startsWith("%")){
                    String methodsignature = head.replace("\n","").trim();
                    if(!methodsignature.isEmpty())
                        KVsignatures.add(methodsignature);
                }
                head = br.readLine();
            }

        }catch (FileNotFoundException e){
            //System.out.println("Response-KV files not found");
        }catch (IOException io){
            //System.out.println("IO Error of reading Response-KV files");
        }
        return KVsignatures;
    }

    private static boolean getNetworkAPI(){
        try{
            String jsonContent = new String(Files.readAllBytes(Paths.get(NetworkDef_FILE)));

            // Read from JSON Strings
            JSONObject jsonObject = new JSONObject(jsonContent);

            POIs = jsonObject;
//            System.out.println(jsonObject.toString());
        } catch (FileNotFoundException e){
            //System.out.println("Response-KV files not found");
        }catch (IOException io){
            //System.out.println("IO Error of reading Response-KV files");
        }
        return true;
    }

}
