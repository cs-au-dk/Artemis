function Brush(canvas)
{
    if(typeof canvas == "string")
        canvas = document.getElementById(canvas);
    
    return buildBrush(canvas);
}


function buildBrush(canvas)
{
    g = {};
    console.log(">>>Brish set!")
    var gfx = canvas.getContext("2d");
    
    g.canvas = canvas;
    g.gfx = gfx;
    g.frameRate = 30;
    g.frameCount = 0;
    
    g.draw = undefined;
    
    var doFill = true;
    var doStroke = true;
    var loopId = 0;
    var loopStarted = false;
    var startMillis = (new Date).getTime();
    
    
    g.size = function(_w, _h)
    {
        g.canvas.width = g.width = _w;
        g.canvas.height = g.height = _h;
    }
    
    g.loopOn = function(drawFunk)
    {
        if(loopStarted)
            clearInterval(loopId);
        
        g.draw = drawFunk;
        
        loopId = setInterval(function(){
            try {
                g.draw();
                g.frameCount++;
            }
            catch(e) {
                clearInterval(loopId);
                throw e;
            }
        }, 1000 / g.frameRate);
        
        loopStarted = true;
    };

    g.setFrameRate = function(fps)
    {
        g.frameRate = fps;
    };
    
    g.millis = function()
    {
        return (new Date).getTime() - startMillis;
    };


    g.beginPath = function()
    {
        gfx.beginPath();
    };
    
    g.endPath = function()
    {
        if(doFill)
            gfx.fill();
        if(doStroke)
            gfx.stroke();
        
        gfx.closePath();
    };
    
    g.moveTo = function(x, y)
    {
        gfx.moveTo(x, y);
        g.lastx = x;
        g.lasty = y;
    };

    g.lineTo = function(x, y)
    {
        gfx.lineTo(x, y);
        g.lastx = x;
        g.lasty = y;
    };
    
    g.bezierTo = function(t, x1, y1, x2, y2, x3, y3)
    {
        if(t == 1.0) {
            gfx.bezierCurveTo(x1,y1, x2,y2, x3,y3);
            g.lastx = x3;
            g.lasty = y3;
        }
        else {  // get part of the curve
            var semi = semiBezier(t, g.lastx,g.lasty, x1,y1, x2,y2, x3,y3);
            
            gfx.bezierCurveTo.apply(gfx, semi);
            
            g.lastx = semi[4];
            g.lasty = semi[5];
        }
    };
    
    g.circle = function(x, y, radius)
    {
        g.beginPath();
        gfx.arc(x, y, radius, 0, Math.PI * 2, false);
        g.endPath();
    };
    
    g.rect = function(x, y, w, h)
    {
        g.beginPath();
        gfx.rect(x, y, width, height);
        g.endPath();
    };
    
    
    g.erase = function()
    {
        gfx.clearRect(0,0, g.width, g.height);
    };
    
    
    g.push = function()
    {
        gfx.save();
    };
    g.pop = function()
    {
        gfx.restore();
    };
    
    
    g.lineWidth = function(w) {
        gfx.lineWidth = w;
    };
    
    g.stroke = function() {
        doStroke = true;
        gfx.strokeStyle = g.color.apply(this, arguments) + "";
    };
    g.fill = function() {
        doFill = true;
        gfx.fillStyle = g.color.apply(this, arguments) + "";
    };
    
    g.noStroke = function() {
        doStroke = false;
    };
    g.noFill = function() {
        doFill = false;
    };
    
    g.color = function(_r, _g, _b, _a)
    {
        if(arguments.length == 2)
            _a = _g;
        else if(arguments.length < 4)
            _a = 255;
        if(arguments.length < 3) {
            _g = _r;
            _b = _r;
        }
        
        return "rgba(" + _r + "," + _g + "," + _b + "," + (_a / 255) + ")";
    };
    
    
    return g;
}