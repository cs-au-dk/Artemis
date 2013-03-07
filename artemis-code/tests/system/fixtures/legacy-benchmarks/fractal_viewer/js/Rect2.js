function Rect2(p1, p2)
{
    this.min = new Vec2(p1.x,p1.y);
    this.max = p2 === undefined ? new Vec2(p1.x,p1.y) : new Vec2(p2.x,p2.y);
    
    this.extent = new Vec2();
    this.center = new Vec2();
    this.hyp = 0;
    
    this.updateExtent();
}
Rect2.prototype =
{
    draw: function()
    {
        g.rect(this.min.x, this.min.y, this.extent.x, this.extent.y);
    },
    
    enclose: function(x, y)
    {
        if(x < this.min.x) this.min.x = x;
        if(y < this.min.y) this.min.y = y;
        
        if(x > this.max.x) this.max.x = x;
        if(y > this.max.y) this.max.y = y;
    },
    
    contains: function(x, y)
    {
        return x > this.min.x && x < this.max.x && y > this.min.y && y < this.max.y;
    },
    
    containsRect: function(rect)
    {
        return (rect.min.x > this.min.x && rect.min.x < this.max.x && rect.min.y > this.min.y && rect.min.y < this.max.y &&
                rect.max.x > this.min.x && rect.max.x < this.max.x && rect.max.y > this.min.y && rect.max.y < this.max.y);
    },
    
    updateExtent: function()
    {
        this.extent.set(
            this.max.x - this.min.x,
            this.max.y - this.min.y
        );
        this.center.set(
            this.min.x + this.extent.x/2,
            this.min.y + this.extent.y/2
        );
        this.hyp = Vec2.mag(this.extent);
    },
    
    transform: function(origin, mv, sc)
    {
        this.min.transform(origin, mv, sc);
        this.max.transform(origin, mv, sc);
        this.center.transform(origin, mv, sc);
        this.extent.mul2(sc);
        this.hyp *= sc;
    }
};
Rect2.intersects = function(r1, r2)
{
    return r1.min.x < r2.max.x && r1.max.x > r2.min.x && r1.min.y < r2.max.y && r1.max.y > r2.min.y;
};