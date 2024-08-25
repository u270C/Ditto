package WebAPIAnalyzer.Models;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * @program: Ditto
 * @description:  Custom object wrapper about Web API
 **/
public class APIEndpoint {

    public String path;
    public HashMap<String, String> queries = new HashMap<>();
    public Set<String> fragments = new HashSet<>();
    public Set<String> httpMethods = new HashSet<>();

    public APIEndpoint(String path) {
        this.path = path;
    }

    public String toString() {
        StringBuilder stringBuilder = new StringBuilder();
        stringBuilder.append("  Path: " + this.path + "\n");
        stringBuilder.append("  Queries: \n");
        for (Map.Entry entry: this.queries.entrySet()) {
            stringBuilder.append("      Query key: " + entry.getKey() + ", query value: " + entry.getValue() + "\n");
        }
        stringBuilder.append("  Fragments: \n");
        for (String entry : this.fragments) {
            stringBuilder.append("      Fragment value: " + entry + "\n");
        }
        stringBuilder.append("  HTTP Methods: \n");
        for (String entry : this.httpMethods) {
            stringBuilder.append("      HTTP Method: " + entry + "\n");
        }
        return stringBuilder.toString();
    }

}
