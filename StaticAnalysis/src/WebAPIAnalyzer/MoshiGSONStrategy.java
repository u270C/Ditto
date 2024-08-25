package WebAPIAnalyzer;

import java.util.Arrays;
import java.util.HashSet;

public class MoshiGSONStrategy {

    public APIAnalyzer analyzer;

    public MoshiGSONStrategy(APIAnalyzer apiAnalyzer) {
        this.analyzer = apiAnalyzer;
    }

    private static HashSet<String> validGSONClasses = new HashSet<>(Arrays.asList(
            "com.google.gson.Gson",
            "Gson",
            "com.google.gson.GsonBuilder",
            "GsonBuilder"));

    private static HashSet<String> validMoshiClasses = new HashSet<>(Arrays.asList(
            "com.squareup.moshi.JsonAdapter",
            "JsonAdapter",
            "com.squareup.moshi.Moshi",
            "Moshi"));

    private static HashSet<String> validSimpleJSONDataTypes = new HashSet<>(Arrays.asList(
            "java.lang.String",
            "java.lang.Double",
            "java.lang.Float",
            "java.lang.Integer",
            "java.lang.Boolean"));

    public boolean isValidGSONType(String typeString) {
        return validGSONClasses.contains(typeString);
    }

    public boolean isValidMoshiType(String typeString) {
        return validMoshiClasses.contains(typeString);
    }

    public boolean isValidSimpleJSONDataType(String typeString) {
        return validSimpleJSONDataTypes.contains(typeString);
    }

}
