function toggle(which, state)
{
    switch(which)
    {
        case "play":
            if(arguments.length == 1)
                state = !playing;
            
            playing = state;
            
            if(playing) {
                if(flower) startFlowerMoment();
                $("#control a.tool").removeClass("selected");
                $("#tog_play").text("pause");
            }
            else {
                playing = false;
                zoomVel = panVel = 0;
                mouseBranch = null;
                $("#tog_play").text("play");
                $("#tool_" + paintTool).addClass("selected");
            }
            break;
        
        case "about":
            if(arguments.length > 1) {
                aboutOn = state;
            }
            else {
                aboutOn = !aboutOn;
                state = aboutOn;
            }
            var about = $("#about");1
            if(aboutOn) {
                about.css({
                    left: window.innerWidth / 2 - (about.width()+28) / 2,
                    top: window.innerHeight / 2 - (about.height()+28) / 2
                });
                $("<div id=\"aboutclear\"></div>").insertBefore(about).one("mousedownw", function(){
                    toggle("about", false);
                    play();
                });
                about.fadeIn(200);
            }
            else {
                $("#aboutclear").remove();
                about.fadeOut(200);
            }
            break;
            
        case "mutate":
            if(arguments.length > 1) {
                mutate = state;
            }
            else {
                mutate = !mutate;
                state = mutate;
            }
            break;
        
        case "flower":
            if(arguments.length > 1) {
                flower = state;
            }
            else {
                flower = !flower;
                state = flower;
            }
            if(flower) {
                if(playing)
                    startFlowerMoment();
            }
            else {
                endFlowerMoment();
            }
            break;
    }
    
    if(state)
        $("#tog_" + which).addClass("selected");
    else
        $("#tog_" + which).removeClass("selected");
    
    return false;
}


function play()
{
    toggle("play", true);
}
function pause()
{
    toggle("play", false);
}


function set_tool(tool)
{
    playing = false;
    paintTool = tool;
    
    $("#control a.tool").removeClass("selected");
    $("#tool_" + paintTool).addClass("selected");
    
    return false;
}

function set_paint_style(style)
{
    playing = false;
    paintStyle = style;
    return false;
}

function reset()
{
    pause();
    initRoot();
    
    fadeBg(0,0,0, 1000);
    
    return false;
}


function fadeBg(r, g, b, dur)
{
    if(fadeBgFading)
        clearInterval(fadeBgTimerId);
    
    fadeBgFrom = clone(bgColor);
    fadeBgStart = (new Date).getTime();
    fadeBgTo = [r, g, b];
    
    fadeBgTimerId = setInterval(function(){
        var time = (new Date).getTime() - fadeBgStart;
        if(time < dur) {
		    for(var i=3; --i >= 0;) {
    		    bgColor[i] = quadOut(time, fadeBgFrom[i], fadeBgTo[i]-fadeBgFrom[i], dur);
		    }
    	}
    	else {
    	    clearInterval(fadeBgTimerId);
    	    bgColor = fadeBgTo;
    	}
    	$(document.body).css("background-color", "rgb(" + Math.floor(bgColor[0]) + "," + Math.floor(bgColor[1]) + "," + Math.floor(bgColor[2]) + ")");
    }, 13);
}
var fadeBgTimerId, fadeBgFading, fadeBgFrom, fadeBgTo, fadeBgStart;