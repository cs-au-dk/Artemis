var
    canvas, container,
    g,
    
    mouse = new Vec2(0,0),
    
    viewBounds,
    cullBounds,
    viewBoundsMax = new Vec2(1000, 500),
    
    root,
    branches = [],
    mouseBranch,
    
    maxLength,
    minLengthToSpawn = 50,
    maxBranches = 100,
    
    origin,
    zoomVel = 0,
    panVel = 0,
    
    bgColor = [0, 0, 0],
    
    playing = false,
    mutate = false,
    flower = false,
    aboutOn = false,
    
    NONE = "none",
    PAINT = "paint",
    ERASE = "erase",
    SPIKE = "spike",
    STROKE = "stroke",
    FLOWER = "flower",
    
    paintTool,
    paintStyle,
    paintRadius = 20,
    
    flowerMoment = false,
    flowerMomentId
;


function justInit()
{
    $("#my_container").fadeIn(500);
    
    canvas = document.getElementById("my_canvas");
    container = document.getElementById("my_container");
    
    canvas.onmousedown = onMouseDown//$(canvas).bind("mousedown", onMouseDown);
    document.onmouseup = onMouseUp//$(document).bind("mouseup", onMouseUp);
    document.onmousemove = onMouseMove//$(document).bind("mousemove", onMouseMove);
    document.onkeydown = onKeyDown//$(document).bind("keydown", onKeyDown);
    
    g = new Brush(canvas);
    g.setFrameRate(30);
    g.loopOn(justDraw);
    
    sizeToWindow();
    origin = new Vec2(viewBounds.center.x, viewBounds.center.y);
    window.onresize = sizeToWindow;
    
    set_tool(NONE);
    set_paint_style(SPIKE);
    toggle("mutate", false);
    toggle("flower", false);
    
    initRoot();
    
    var hash = window.location.hash.substring(1);
    if(hash == "play")
        toggle("play", true);
    else
        toggle("about", true);
};
window.onload = justInit;

function initRoot()
{
    clearBranches();
    
    root = new Branch({
        style: paintStyle,
        twigRule: {
            nbr:    [8],
            ncv:    [16, 16, 16, 16],
            angle:  [rand2(-Math.PI, Math.PI) * 0.33],
            crook:  [0.1],
            side:   [0, 1],
            style:  [SPIKE],
            len:    [1, 1, 1, 1],
            flower: false
        }
    });
    root.gen({
        pos:    new Vec2(g.width*rand2(0.25,0.75), g.height),
        angle:  -Math.PI / 2,
        crook:  0.05,
        len:    g.height,
        weight: 0.04,
        ncv:    16
    });
    addBranch(root);
}

function sizeToWindow()
{
    var winw = window.innerWidth;
    var winh = window.innerHeight;
    
    viewBounds = new Rect2(
        new Vec2(0,0),
        new Vec2(Math.min(winw, viewBoundsMax.x), Math.min(winh, viewBoundsMax.y))
    );
    cullBounds = new Rect2(
        new Vec2(viewBounds.min.x - 50, viewBounds.min.y - 50),
        new Vec2(viewBounds.max.x + 50, viewBounds.max.y + 50)
    );
    maxLength = viewBounds.hyp * 10;
    g.size(viewBounds.extent.x, viewBounds.extent.y);
    
    // adjust css
    container.style.left = winw/2 - viewBounds.extent.x/2;
    container.style.top = winh/2 - viewBounds.extent.y/2;
}



// DISPLAY

function justDraw()
{
    g.erase();
    
    g.noFill();
    g.stroke(0);
    for(var i=0, brl=branches.length; i < brl; i++) {
        branches[i].update();
        branches[i].draw();
    }
    if(mouseBranch) {
        mouseBranch.update();
        mouseBranch.draw();
    }
    
    
    // get the closest branch to the mouse
    
    sortByClosestToMouse();
    var closest = branches[0];
    if(closest) {
        var ccv = closest.cv[Math.floor(closest.cv.length / 2)];
        origin.set(
            lerp(origin.x, ccv.x, 0.25),
            lerp(origin.y, ccv.y, 0.25)
        );
    }
    
    
    // transform the scene
    
    if(playing && closest) {
        var move = new Vec2(
            (viewBounds.center.x-origin.x) * panVel,
            (viewBounds.center.y-origin.y) * panVel
        );
        for(var i = branches.length; --i >= 0;) {
            branches[i].transform(origin, move, 1 + zoomVel);
        }
        
        var speedy = mouse.down && closest.style != FLOWER;
        
        zoomVel *= 0.9;
        zoomVel += lerp(0.001, speedy ? 0.01 : 0.002, branches.length / maxBranches);
        
        panVel *= 0.9;
        panVel += lerp(0.001, speedy ? 0.005 : 0.002, branches.length / maxBranches);
    }
    
    
    cullOffscreen();
}

// END DISPLAY



function startFlowerMoment()
{
    if(flowerMoment)
        clearTimeout(flowerMomentId);
    
    if(playing) {
        flowerMoment = true;
        flowerMomentId = setTimeout(endFlowerMoment, randInt2(5000,20000));
    
        fadeBg(randInt(130), randInt(130), randInt(130), 1000);
    }
}
function endFlowerMoment()
{
    if(flowerMoment) {
        flowerMoment = false;
        clearTimeout(flowerMomentId);
    }
    
    if(flower)
        flowerMomentId = setTimeout(startFlowerMoment, randInt2(8000,12000));
}



// MOUSE INTERACTION

function onMouseDown(e)
{
    mouse.down = true;
}

function onMouseMove(e)
{
    mouse.set(e.pageX-container.offsetLeft, e.pageY-container.offsetTop);
    
    /*if(mouse.down && !playing) {
        switch(paintTool)
        {
            case PAINT:
                if(mouseBranch) {
                    var lastCv = mouseBranch.cv[mouseBranch.cv.length-1];
                    if(Vec2.distSq(lastCv, mouse) > 20*20) {
                        mouseBranch.pushCv(new Vec2(mouse.x, mouse.y));
                        mouseBranch.bake();
                    }
                }
                break;
                
            case ERASE:
                var selrect = new Rect2(
                    new Vec2(mouse.x - paintRadius, mouse.y - paintRadius),
                    new Vec2(mouse.x + paintRadius, mouse.y + paintRadius)
                );
                for(var i=branches.length; --i >= 0;) {
                    var br = branches[i];
                    if(Rect2.intersects(br.bounds, selrect)) {
                       for(var j=br.cv.length-1; --j >= 0;) {
                           if(segCircIntersects(br.cv[j], br.cv[j+1], mouse, paintRadius)) {
                               removeBranch(br);
                               break;
                           }
                       }
                    }
                }
                break;
        }
    }*/
}

function onMouseUp(e)
{
    mouse.down = false;
    /*if(mouseBranch) {
        if(mouseBranch.cv.length < 2) {
            removeBranch(mouseBranch);
            mouseBranch = null;
        }
    }*/
}

function onKeyDown(e)
{
	var c = e.charCode
    alert(">>>275 " + c);
	switch(c) {
        case ' ':
        case 'p':
            toggle('play');
            break;
        
        case 'n':
            reset();
            break;
        
        case 'm':
            toggle('mutate');
            break;
        
        case 'b':
            toggle('flower');
            break;
        
        case 'a':
            toggle('about');
            break;
    }
}



function addBranch(br)
{
    branches.push(br);
}
function removeBranch(br)
{
    removeBranchByIndex(branches.indexOf(br));
}
function removeBranchByIndex(i)
{
    branches[i].prune();
    if(i >= 0)
        branches.splice(i, 1);
}
function clearBranches()
{
    for(var i=branches.length; --i>=0;)
        branches[i].prune();
    branches = [];
}



function cullOffscreen()
{
    for(var i=branches.length; --i>=0;) {
        var br = branches[i];
        if(!Rect2.intersects(cullBounds, br.bounds) || br.bounds.hyp > maxLength) {
            removeBranchByIndex(i);
        }
    }
}



function findIntersection(p1, p2)
{
    var bounds = new Rect2(
        new Vec2(Math.min(p1.x, p2.x), Math.min(p1.y, p2.y)),
        new Vec2(Math.max(p1.x, p2.x), Math.max(p1.y, p2.y))
    );
    
    for(var i=branches.length; --i>=0;) {
        var br = branches[i];
        if(Rect2.intersects(bounds, br.bounds)) {
            for(var j = br.cv.length-1; --j >= 0;) {
                var is = segIntersection(p1, p2, br.cv[j], br.cv[j+1]);
                if(is !== null)
                    return is;
            }
        }
    }
    
    return null;
}


function sortByClosestToMouse()
{
    // set distances
    for(var i = branches.length; --i >= 0;) {
        var ctr_cv = branches[i].cv[Math.floor(branches[i].cv.length / 2)];
        branches[i].distToMouse = Vec2.distSq(mouse, ctr_cv);
    }
    
    // sort the array
    branches.sort(sortMouseDist);
}
function sortMouseDist(a, b) {
    return b.distToMouse < a.distToMouse && b.bounds.hyp < viewBounds.hyp ? 1 : -1;
}