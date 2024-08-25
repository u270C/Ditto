# URL Shortening Service Interface Testing

## Introduction
Ditto originated from a scientific research project whose goal was to analyze the security of dedicated URL shortening services. It is being open-sourced to promote the health of the security community and to build more secure short-link services. 
>Disclaimer: All use of Ditto for malicious activities is prohibited.


## Project Structure
Overarching Goal

This repository contain the following modules:
1. DUSS API Static Analysis
2. DUSS API Vulnerability Detection

```
├── README.md
├── StaticAnalysis # Static API Analysis of Ditto
│    ├── res  # This folder contians basic project condiguraiton files, include ICC handler and Network Library API signatures.
│    │   ├── AndroidCallbacks.txt
│    │   ├── EasyTaintWrapperSource.txt
│    │   ├── IPCMethods.txt
│    │   ├── IccLinksConfigFile.txt
│    │   ├── NetworkAPI.json
│    │   ├── NetworkAPIRequest.txt
│    │   ├── NetworkAPIResponse.txt
│    │   ├── androidClassPrefixes.list
│    │   ├── androidClasses.list
│    │   ├── iccta.properties
│    │   └── networkcallback.txt
│    └── src  # The source code of API Inference
│        ├── WebAPIAnalyzer  # Main logic of DUSS API extraction (include )
│        │   ├── APIAnalyzer.java  # Extract the Web API call stacks
│        │   ├── APIURLStrategy.java # The default URL extration strategy
│        │   ├── GdmStrategy.java 
│        │   ├── Models # Basic Data Structure Models
│        │   │   ├── APIEndpoint.java
│        │   │   └── APIURL.java
│        │   ├── MoshiGSONStrategy.java # Match MoshiGSON data structure
│        │   ├── ORGJSONStrategy.java # Match ORGJSON data structure
│        │   ├── OkHttpStrategy.java # URL extraction strategy for Okhttp
│        │   ├── RetrofitStrategy.java # URL extraction strategy for Retrofit
│        │   ├── Snippet.java # Data structure of POI call stacks
│        ├── analyze
│        │   └── Main.java  # Main function of StaticAnalysis
│        ├── cfg # Utils for building control-flow graph
│        │   ├── CfgFactory.java
│        │   └── Path.java
│        ├── cg # Utils for building call graph with inter-procedure analysis
│        │   ├── CallGraphUtils.java
│        │   ├── ICFG.java
│        │   └── UnitSelect.java
│        ├── component
│        │   ├── EntryPointAnalyze.java # Analyze the total entrypoints of an Android app
│        │   ├── FragementCreater.java # Analyze Android fragments
│        │   └── ResolveManifest.java # Analyze Android Manifest files in APK
│        ├── constant 
│        │   ├── ApkAndJavaConstants.java 
│        │   ├── EntryPointsDefinition.java
│        │   ├── IPCPointDefinition.java
│        │   └── NetworkAPIDefinition.java
│        ├── dataflow # Utils for building data-flow graph, and perform backward/forward analysis.
│        │   ├── AbstractDataFlow.java
│        │   ├── AccessPathTag.java
│        │   ├── Analyze.java
│        │   ├── BackwardDataFlow.java
│        │   ├── CallSite.java
│        │   ├── DataFlowEngine.java
│        │   ├── Event.java
│        │   ├── EventQueue.java
│        │   ├── FileInfo.java
│        │   ├── FileType.java
│        │   ├── ForwardDataFlow.java
│        │   ├── Point.java
│        │   ├── RuleChecker.java
│        │   └── TaintWrapper.java
│        └── util # Utils for the default project configuration.
│            ├── DirTraversal.java
│            ├── Log.java
│            ├── SootInit.java
│            └── StringUtil.java
├── frida-module.js #
└── TestApk # Demo app

```

## Project Dependencies

This project relies on several open source projects, including Soot (4.6.0), TextExerciser, and Frida. To run Ditto, configure and build the code according to the corresponding project requirements.