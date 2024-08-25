package WebAPIAnalyzer;

import soot.JastAddJ.FieldDeclaration;

import java.util.List;

public class ORGJSONStrategy {

    private APIAnalyzer analyzer;

    public boolean isJSONObject(String typeString){
        if(typeString.split("\\.")[-1].equals("JSONObject")){
            return true;
        }
        return false;
    }

}
