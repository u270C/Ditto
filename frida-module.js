// frida -U -f [packagename] -l a.js --no-pause
// Hook the URL_Getter method (provenance of URL object of request body)
// class name of URL_Getter
let classNameG = "";
// method name of URL_Getter
let methodNameG = "i";
// parameter types of URL_Getter
let paramTypesG = ['int', 'java.lang.String'];
// URL object to be altered.
let urlParamIndex = 1;

// Hook the response callback method
let classNameA = "";
let methodNameA = "response";
let paramTypesA = ['java.lang.String'];

let responseValue = ""; // Store the value of `response`
let state = 0;


// This function will be triggered with the dynamic execution of the program, 
// and select the variation of the URL according to different modes, so as to carry out security tests
function changeUrl(url, mode) {
    let urlObj = new URL(url);

    switch (mode) {
        case 0:
            break;
        case 1:
            // URL scheme -> javascript
            urlObj.protocol = "javascript";
            urlObj.host += "/%0a%0dalert(1);";
            break;
        case 2:
            // URL host -> evil.com
            urlObj.host = "evil.com";
            break;
        case 3:
            // URL host + \evil.com
            urlObj.host += "\\evil.com";
            break;
        case 4:
            // URL host + @evil.com
            urlObj.host += "@evil.com";
            break;
        case 5:
            // URL host + \@evil.com
            urlObj.host += "\\@evil.com";
            break;
        case 6:
            // URL host add prefix
            urlObj.host = "aaa" + urlObj.host;
            break;
        case 7:
            // a:a@www.malicious.com:b@www.benign.com
            urlObj.host = "a:a@" + urlObj.host + ":b@" + "evil.com";
            break;
        case 8:
            // URL+#
            urlObj.href = urlObj.origin + "#" + urlObj.host;
            urlObj.host = "evil.com"
        case 9:
            // detect startWith
            urlObj.host += ".evil.com";
        case 10:
            //  TDCDetect use code injection tools to check whether the URL is vulnerable to open-redirection/XSS injection....
            url = TDCDetect(url);  // Need self implements.
            return url;
        case 11:
            // URL scheme -> %0Ajavascript
            urlObj.protocol = "%0Ajavascript";
            urlObj.host += "/%0a%0dalert(1);";
            break;
        default:
            break;
    }

    return urlObj.toString();
}


Java.perform(function () {
    var classG = Java.use(classNameG);
    var classA = Java.use(classNameA);
    
    // Hook URL_Getter method, and modify the URL value.
    classG[methodNameG].overload(...paramTypesG).implementation = function () {
        let args = Array.prototype.slice.call(arguments);
     
        if (typeof args[urlParamIndex] === 'string') {
            args[urlParamIndex] = changeUrl(args[urlParamIndex], state);
        }
        
        console.log(`${methodName} is called with modified URL: ${args[urlParamIndex]}`);
        
        return this[methodNameG].apply(this, args);
    };
    
    // Hook response callback, and record the responsed URL.
    classA[methodNameA].overload(...paramTypesA).implementation = function (responseString) {
        console.log(`${methodNameA} is called with response: ${responseString}`);
        
        let result = this[methodNameA](responseString);

        // store response
        responseValue = result;
        if(state > 0) 
        {
            let originObj = new URL(responseValue);
            let curObj = new URL(result);
            if(originObj.host == curObj.host)
                console.log(state)
            else state = state + 1;
        }

        return result;
    };
});
