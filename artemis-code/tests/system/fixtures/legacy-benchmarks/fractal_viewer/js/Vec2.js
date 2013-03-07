function Vec2(_x, _y)
{
    this.x = _x;
    this.y = _y;
}
Vec2.prototype =
{
    set: function(_x, _y)
    {
        this.x = _x;
        this.y = _y;
    },
    
    add: function(v)
    {
        this.x += v.x;
        this.y += v.y;
    },
    add2: function(_x, _y)
    {
        this.x += _x;
        this.y += _y === undefined ? _x : _y;
    },
    
    mul2: function(_x, _y)
    {
        this.x *= _x;
        this.y *= _y === undefined ? _x : _y;
    },
    
    transform: function(origin, mv, sc, rot)
    {
        var xo = (this.x - origin.x + mv.x) * sc;
        var yo = (this.y - origin.y + mv.y) * sc;
        if(rot) {
            this.x = origin.x + (xo*Math.cos(rot) - yo*Math.sin(rot));
            this.y = origin.y + (xo*Math.sin(rot) + yo*Math.cos(rot));
        }
        else {
            this.x = origin.x + xo;
            this.y = origin.y + yo;
        }
    },
    
    normalize: function()
    {
        var m = Math.sqrt(this.x*this.x + this.y*this.y);
        if(m != 0) {
            this.x /= m;
            this.y /= m;
        }
    },
    
    equals: function(v)
    {
        return x == v.x && y == v.y;
    }
};
Vec2.dist = function(v1, v2)
{
    return Math.sqrt(Vec2.distSq(v1,v2));
};
Vec2.distSq = function(v1, v2)
{
    return distSq(v1.x,v1.y, v2.x,v2.y);
};
Vec2.mag = function(v)
{
    return Math.sqrt(v.x*v.x + v.y*v.y);
};
Vec2.angle = function(v)
{
    return Math.atan2(v.y, v.x);
};
Vec2.copy = function(v)
{
    return new Vec2(v.x, v.y);
};
Vec2.fromAngOff = function(x, y, angle)
{
    var c = Math.cos(angle);
    var s = Math.sin(angle);
    return new Vec2(x*c - y*s, x*s + y*c);
};