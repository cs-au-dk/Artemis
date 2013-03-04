function Leaf(pos, rot, len)
{
    this.pos = pos;
    this.rot = rot;
    
    this.vel = new Vec2(0,0);
    this.rotvel = 0;
    
    var l2 = len * rand2(0.2, 0.3);
    
    this.bez = [
        new Vec2(0,0),
        new Vec2(len * 0.333, l2),
        new Vec2(len * 0.666, l2),
        new Vec2(len, 0),
        new Vec2(len * 0.666, -l2),
        new Vec2(len * 0.333, -l2),
        new Vec2(0,0)
    ];
}

Leaf.prototype =
{
    attached: true,
    udeath: 0,
    
    update: function()
    {
        if(!this.attached) {
            this.udeath = Math.min(1, (g.millis() - this.detachTime) / this.pruneDelay);
            
            if(this.udeath == 1) {
                this.prune();
            }
            else {
                this.pos.add(this.vel);
                this.rot += this.rotvel;
            }
        }
    },
    
    draw: function(scale)
    {
        if(!this.attached)
            scale *= 1 - this.udeath;
        
        g.push();
        g.gfx.translate(this.pos.x, this.pos.y);
        g.gfx.rotate(this.rot);
        g.gfx.scale(scale, scale);
        
        g.beginPath();
        g.gfx.moveTo(this.bez[0].x, this.bez[0].y);
        g.gfx.bezierCurveTo(
            this.bez[1].x, this.bez[1].y,
            this.bez[2].x, this.bez[2].y,
            this.bez[3].x, this.bez[3].y
        );
        g.gfx.bezierCurveTo(
            this.bez[4].x, this.bez[4].y,
            this.bez[5].x, this.bez[5].y,
            this.bez[6].x, this.bez[6].y
        );
        g.endPath();
        
        g.pop();
    },
    
    transform: function(origin, mv, sc)
    {
        this.pos.transform(origin, mv, sc);
        this.vel.mul2(sc);
        for(var i = this.bez.length; --i >= 0;)
            this.bez[i].mul2(sc);
    },
    
    detach: function()
    {
        var mag = rand2(0.025, 0.1);
        this.vel.set(rotx(this.bez[3].x, this.rot) * mag, roty(this.bez[3].x, this.rot) * mag);
        this.rotvel = rand2(-0.1, 0.1);
        
        this.attached = false;
        this.detachTime = g.millis();
        this.pruneDelay = randInt2(500, 1000);
    },
    
    prune: function()
    {
        if(this.parent)
            this.parent.removeLeaf(this);
    }
}