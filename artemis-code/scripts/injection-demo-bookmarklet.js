javascript:(function() {

/*
 * Injection Demo Bookmarklet
 * 
 * Loads a file from the injection logs (see /tmp/injections) and replays that injection into the site.
 * You must already be on the appropriate page for the site, as if we loaded the page here, this script would be lost.
 */

var delayTime = 1500; // Delay between actions in ms
var fieldColour = "#ff0"; // All fields
var injectColour = "#0f0"; // Fields to be injected
var injectNowColour = "#f00"; // Field currently being injected
var buttonColour = "#00f"; // Entry-point
var buttonClickColour = "#f00"; // Entry-point while being clicked


/*
 * Prompt the user for a log file and replay that injection.
 */
function main() {
    askForFileAndRun();
}


/*
 * Replays a given injection log.
 */
function replayInjection(log) {
    // Locate and mark the EP.
    var ep;
    if(log.entrypoint == "auto") {
        // TODO: This is quite different from the implementation in entrypoints.cpp
        ep = document.querySelector("button, input[type='button'], input[type='submit'], input[type='image']");
        if(!ep) {
            error("Could not locate any candidate entry-points.", true);
            return;
        }
    } else {
        var buttons = document.evaluate(log.entrypoint, document, null, XPathResult.UNORDERED_NODE_SNAPSHOT_TYPE, null);
        if(buttons.snapshotLength != 1) {
            error("Could not locate entry-point, " + buttons.length + " elements matched the given XPath.", true);
            return;
        }
        ep = buttons.snapshotItem(0);
    }
    highlight(ep, buttonColour);
    
    delay(function(){
        // Mark the fields.
        highlightAllFields();
    });
    
    delay(function() {
        fieldsToInject = log.injection.map(function(x){ return x.field });
        highlightInjectedFields(fieldsToInject);
    });
    
    // Inject the fields one-by-one
    // They include their own delay() calls.
    log.injection.forEach(singleInjection);
    
    delay(function() {
        highlight(ep, buttonClickColour);
    });
    
    delay(function() {
        // Click the button
        // TODO: Should really set up a proper MouseEvent etc. for this and click the coordinates given by getCoordinates(ep) in order to be closer to the behaviour of Artemis.
        //coords = getCoordinates(ep);
        ep.click();
    });
    
}

/*
 * Injects a single value into a field.
 */
function singleInjection(inject) {
    var field = document.getElementById(inject.field);
    if(!field) {
        error("Cannot locate field '" + inject.field + "'.", false);
        return;
    }
    
    delay(function() {
        highlight(field, injectNowColour);
    });
    
    delay(function() {
        injectValue(field, inject.value);
    });
    
    delay(function() {
        // Trigger handler as in formfieldinjector.cpp
        var event = document.createEvent('HTMLEvents');
        event.initEvent('change', false, true);
        field.dispatchEvent(event);
    });
    
    delay(function() {
        highlight(field, injectColour);
    });
}

/*
 * Performs the injection into different field types.
 */
function injectValue(field, value) {
    // TODO: Not perfect, and not a perfect match for our real injection.
    
    switch(typeof(value)) {
        case "boolean":
            field.checked = value;
            break;
        
        case "number":
            field.selectedIndex = value;
            break;
        
        case "string": // Fall-through
        default:
            field.value = value;
            break;
    }
}

/*
 * Highlight a single field.
 */
function highlight(el, colour) {
    el.style.outline = "5px solid " + colour;
}

/*
 * Highlight all form fields found on the page.
 */
function highlightAllFields() {
    // Same logic as used in executionresultbuilder.cpp
    
    // Convert to arrays
    var inputs = Array.prototype.slice.call(document.getElementsByTagName("input"));
    var texts = Array.prototype.slice.call(document.getElementsByTagName("textarea"));
    var selects = Array.prototype.slice.call(document.getElementsByTagName("select"));
    
    var goodInputs = inputs.filter(function(x, idx, arr) {
        var badTypes = ["button", "hidden", "submit", "reset", "image"];
        if(badTypes.indexOf(x.type) > -1) {
            return false;
        } else {
            return true;
        }
    });
    
    var fields = [].concat(goodInputs, texts, selects);
    
    fields.forEach(function(f) {
        highlight(f, fieldColour);
    });
}

/*
 * Highlights the fields selected for injection.
 */
function highlightInjectedFields(fieldIds) {
    fieldIds.forEach(function(id) {
        elem = document.getElementById(id);
        if(elem) {
            highlight(elem, injectColour);
        }
    });
}

/*
 * Handle errors
 */
function error(message, fatal) {
    alert(message);
    // TODO: if not fatal, then only log.
}

/*
 * Handle delays.
 * The passed function willbe called at a suitable later time.
 * Returns immediately.
 * Subsequent calls will have a delay between them.
 * This is really a complete hack and assumes the main code runs quickly.
 */
var nextEvent = 0;
function delay(callback) {
    nextEvent += delayTime;
    window.setTimeout(callback, nextEvent);
}

/*
 * Look up the coordinates of a certain element.
 * Adapted from clickinput.cpp
 */
/*
function getCoordinates(element) {
    function findPos(obj) {
        var l = 0;
        var t = 0;
        do {
            l += obj.offsetLeft;
            t += obj.offsetTop;
        } while(obj = obj.offsetParent);
        return [l, t];
    }
    
    var bb = element.getBoundingClientRect();
    var width = bb.right - bb.left;
    var height = bb.bottom - bb.top;
    var absPos = findPos(element);
    var clickX = absPos[0] + width/2;
    var clickY = absPos[1] + height/2;
    return {"x": Math.floor(clickX), "y": Math.floor(clickY)];
}
*/




function askForFileAndRun() {
    var input = document.createElement("input");
    input.type = "file";
    input.id = "ArtFormFileInput";
    
    document.body.appendChild(input);
    
    // Pretend to click on the file control to open the window.
    // Seems this doesn't work (security?)
    //event = document.createEvent('MouseEvents');
    //event.initEvent('click', false, true);
    //input.dispatchEvent(event);
    
    // position the element in the top left instead...
    input.style.position = "absolute";
    input.style.top = "0";
    input.style.left = "50%";
    input.style.background = "white";
    input.style.border = "20px solid orange";
    
    function handleFileSelect(event) 
    {
        //input.style.display = "none";
        
        var files = event.target.files;
        var reader = new FileReader();
        
        reader.onload = function() {
            var text = reader.result;
            
            input.parentElement.removeChild(input);
            
            var log = JSON.parse(text);
            replayInjection(log);
        }
        
        reader.readAsText(files[0]);
    }
    
    input.addEventListener("change", handleFileSelect)
}




main();


})();