// HELPER FUNCTIONZ

function lerp(a, b, u)
{
    return a + (b-a)*u;
}
function map(v, in_min, in_max, out_min, out_max)
{
    return out_min + (out_max-out_min) * ((v-in_min) / (in_max-in_min));
}


function randInt(max)
{
    return Math.floor(Math.random() * max);
}
function randInt2(min, max)
{
    return Math.floor(min + Math.random() * (max-min));
}
function rand(max)
{
    return Math.random() * max;
}
function rand2(min, max)
{
    return min + Math.random() * (max-min);
}


function clamp(v, min, max)
{
    return v < min ? min : (v > max ? max : v);
}

function wrap(v, min, max)
{
    if(v < min) return max - (min-v) % (max-min);
    else if(v >= max) return (v-min) % (max-min) + min;
    else return v;
}


function distSq(x1, y1, x2, y2)
{
    var xo = x2 - x1;
    var yo = y2 - y1;
    return xo*xo + yo*yo;
}
function dist(x1, y1, x2, y2)
{
    return Math.sqrt(distSq(x1,y1, x2,y2));
}


function rotx(x, angle)
{
    return x * Math.cos(angle);
}
function roty(y, angle)
{
    return y * Math.sin(angle);
}


function bezierPoint(a, b, c, d, t)
{
    var t1 = 1.0 - t;
    return a*t1*t1*t1 + 3*b*t*t1*t1 + 3*c*t*t*t1 + d*t*t*t;
}


function segIntersection(p1, p2, p3, p4)
{
    var bx = p2.x - p1.x;
    var by = p2.y - p1.y;
    var dx = p4.x - p3.x;
    var dy = p4.y - p3.y;
    
    var b_dot_d_perp = bx*dy - by*dx;
    
    if(b_dot_d_perp == 0) return null;
    
    var cx = p3.x-p1.x;
    var cy = p3.y-p1.y;
    
    var t = (cx*dy - cy*dx) / b_dot_d_perp;
    if(t<0 || t>1) return null;
    
    var u = (cx*by - cy*bx) / b_dot_d_perp;
    if(u<0 || u>1) return null;
    
    return new Vec2(p1.x + t*bx, p1.y + t*by);
}

function segCircIntersects(l1, l2, cp, cr)
{
    var u = ((cp.x-l1.x)*(l2.x-l1.x) + (cp.y-l1.y)*(l2.y-l1.y)) / ((l2.x-l1.x)*(l2.x-l1.x) + (l2.y-l1.y)*(l2.y-l1.y));
    
    if(u<0) return Vec2.distSq(l1, cp) < cr*cr;
    if(u>1) return Vec2.distSq(l2, cp) < cr*cr;

    var ox = l1.x + (l2.x-l1.x)*u - cp.x;
    var oy = l1.y + (l2.y-l1.y)*u - cp.y;

    return ox*ox + oy*oy <= cr*cr;
}


function curveSegmentBez(v1, v2, v3, v4, s)
{
    return [
        new Vec2(v2.x + (s*v3.x - s*v1.x)/6, v2.y + (s*v3.y - s*v1.y)/6),
        new Vec2(v3.x + (s*v2.x - s*v4.x)/6, v3.y + (s*v2.y - s*v4.y)/6),
        new Vec2(v3.x, v3.y)
    ];
}

function semiBezier(t, x0, y0, x1, y1, x2, y2, x3, y3)
{
    if(t == 0.0) {
        return [x0,y0, x0,y0, x0,y0];
    }
    else if(t == 1.0) {
        return [x1,y1, x2,y2, x3,y3];
    }
    
    var qx1 = x0 + (x1-x0)*t;
    var qy1 = y0 + (y1-y0)*t;
    var qx2 = x1 + (x2-x1)*t;
    var qy2 = y1 + (y2-y1)*t;
    var qx3 = x2 + (x3-x2)*t;
    var qy3 = y2 + (y3-y2)*t;
    var rx2 = qx1 + (qx2-qx1)*t;
    var ry2 = qy1 + (qy2-qy1)*t;
    var rx3 = qx2 + (qx3-qx2)*t;
    var ry3 = qy2 + (qy3-qy2)*t;
    var bx3 = rx2 + (rx3-rx2)*t;
    var by3 = ry2 + (ry3-ry2)*t;
    
    return [qx1, qy1, rx2, ry2, bx3, by3];
}


function clone(obj)
{
    if(obj == null || typeof(obj) != 'object')
        return obj;
    
    var temp = new obj.constructor();
    for(var key in obj)
        temp[key] = clone(obj[key]);
    
    return temp;
}


Array.prototype.indexOf = function(elem) {
    for(var i = 0; i < this.length; i++)
        if(this[i] === elem)
            return i;
    return -1;
}


// EEEEASING

function quadIn(t, b, c, d) {
    return c*(t/=d)*t + b;
}
function quadOut(t, b, c, d) {
    return -c *(t/=d)*(t-2) + b;
}
function quadInOut(t, b, c, d) {
    if((t/=d/2) < 1)
        return c/2*t*t + b;
    return -c/2 * ((--t)*(t-2) - 1) + b;
}

function linearNone(t, b, c, d) {
    return c*t/d + b;
}