package WebAPIAnalyzer.Models;

import java.util.HashSet;

/**
 * @program: Ditto
 * @description:  Custom API URL data structure
 **/
public class APIURL {

    public String path;
    public String scheme;
    public String authority;
    public String library;
    public HashSet<APIEndpoint> endpoints = new HashSet<>();

    public APIURL(String scheme) {
        this.scheme = scheme;
    }

    public String getBaseURL() {
        return scheme + authority;
    }

    public String toString() {
        StringBuilder stringBuilder = new StringBuilder();
        stringBuilder.append("Path: \n" + this.path + "\n");
        stringBuilder.append("Library: \n" + this.library + "\n");
        stringBuilder.append("Scheme: \n" + this.scheme + "\n");
        stringBuilder.append("Authority: \n" + this.authority + "\n");
        stringBuilder.append("Base URL: \n" + getBaseURL() + "\n");
        stringBuilder.append("Endpoints: \n");
        for (APIEndpoint endpoint : this.endpoints) {
            stringBuilder.append(endpoint.toString());
        }
        stringBuilder.append("=========================API URL=========================\n");
        return stringBuilder.toString();
    }

}
