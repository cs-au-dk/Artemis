function Branch(ops)
{
    this.growDur = randInt2(250,750);
    this.birthTime = g.millis();
    
    this.cv = [];
    this.nrm = [];
    this.bez = [];
    this.sub = [];
    this.leaves = [];
    
    if(ops) {
        for(var key in ops) {
            this[key] = ops[key];
        }
    }
}


Branch.prototype =
{
    color: [255, 255, 255, 255],
    style: SPIKE,
    
    ugrow: 0,
    uease: 0,
    
    finished: false,
    
    gen: function(ops)
    {
        // init properties
        this.cv = [];
        this.weight = ops.weight;

        var
            ncv1 = ops.ncv - 1,
            ang  = ops.angle,
            angv = 0,
            cv1  = clone(ops.pos),
            cv2
        ;
        
        // make cvs
        this.pushCv(cv1);
        for(var i=0; i < ncv1; i++) {
            cv2 = new Vec2(
                cv1.x + rotx(ops.len/ncv1, ang),
                cv1.y + roty(ops.len/ncv1, ang)
            );
            
            angv += rand2(-ops.crook, ops.crook);
            ang += angv;
            
            // grow up the y axis
            if(this.style == FLOWER) {
                ang += wrap(ang + Math.PI*0.5, -Math.PI, Math.PI) * -0.2;
            }
            
            var is = findIntersection(cv1, cv2);
            
            if(is && i != 0) {
                this.pushCv(is);
                break;
            }
            else {
                this.pushCv(cv2);
            }

            cv1 = cv2;
        }
        
        // bake curve and bounds
        this.bake();
        
        // make leaves
        if(flower && flowerMoment && this.twigRule) {//} && this.twigRule.flower) {
            var tr = this.twigRule;
            var n = Math.floor(tr.nbr[0]);
            for(var i=0; i < n; i++) {
                var side = Math.round(1 - tr.side[i % tr.side.length])
                this.leaf(
                    (i + 1) / (n + 1),
                    side ? tr.angle[i % tr.angle.length] : Math.PI - tr.angle[i % tr.angle.length]
                );
            }
        }
    },
    
    update: function()
    {
        // call something when done growing
        var time = g.millis() - this.birthTime;
        this.ugrow = time > this.growDur ? 1 : linearNone(time, 0,1, this.growDur);
        this.uease = time > this.growDur ? 1 : quadOut(time, 0,1, this.growDur);
        
        if(this.parent)
            this.ugrow = Math.max(0, this.ugrow - (1 - Math.min(1, this.parent.ugrow/this.upos)));
        
        if(
            this.twigRule && this.sub.length == 0 && this.ugrow >= 1 &&
            this.bounds.hyp >= minLengthToSpawn && this.bounds.hyp < viewBounds.hyp
        ){
            this.multiTwig();
        }
        
        for(var i=this.leaves.length; --i >= 0;)
            this.leaves[i].update();
    },
    
    draw: function()
    {
        this.color[3] = Math.min(255, map(this.bounds.hyp, maxLength*0.8,maxLength, 255,0));
        
        Branch.draw_spike(this);
        
        for(var i=this.leaves.length; --i >= 0;)
            this.leaves[i].draw(this.uease);
    },
    
    
    pushCv: function(v)
    {
        this.cv.push(v);
    },
    
    popCv: function()
    {
        return this.cv.pop();
    },
    
    
    addSub: function(br)
    {
        br.parent = this;
        this.sub.push(br);
    },
    
    removeSub: function(br)
    {
        br.parent = null;
        var i = this.sub.indexOf(br);
        if(i >= 0)
            this.sub.splice(i, 1);
    },
    
    addLeaf: function(leaf)
    {
        leaf.parent = this;
        this.leaves.push(leaf);
    },
    
    removeLeaf: function(leaf)
    {
        leaf.parent = null;
        var i = this.leaves.indexOf(leaf);
        if(i >= 0)
            this.leaves.splice(i, 1);
    },
    
    
    transform: function(origin, mv, sc)
    {
        for(var i = this.cv.length; --i >= 0;)
            this.cv[i].transform(origin, mv, sc);
        for(var i = this.bez.length; --i >= 0;)
            this.bez[i].transform(origin, mv, sc);
        this.bounds.transform(origin, mv, sc);
        
        for(var i=this.leaves.length; --i >= 0;)
            this.leaves[i].transform(origin, mv, sc);
    },
    
    
    bake: function()
    {
        this.updateNormals();
        this.updateBezier();
        this.updateBounds();
    },
    
    updateBezier: function()
    {
        var s = 1;
        var cvl1 = this.cv.length - 1;
        
        // first bezier point is the first cv
        this.bez = [clone(this.cv[0])];
        
        this.bez.push.apply(this.bez, curveSegmentBez(this.cv[0],this.cv[0],this.cv[1],this.cv[2], s));
        for(var i=1; i < cvl1-1; i++) {
            this.bez.push.apply(this.bez, curveSegmentBez(this.cv[i-1],this.cv[i],this.cv[i+1],this.cv[i+2], s));
        }
        this.bez.push.apply(this.bez, curveSegmentBez(this.cv[cvl1-2],this.cv[cvl1-1],this.cv[cvl1],this.cv[cvl1], s));
    },
    
    updateNormals: function()
    {
        this.nrm = [];
        for(var i=0, cvl=this.cv.length; i < cvl; i++) {
            this.nrm[i] = new Vec2(0,0);
            if(i > 0)
                this.nrm[i].add2(
                    -(this.cv[i].y - this.cv[i-1].y),
                    this.cv[i].x - this.cv[i-1].x
                );
            if(i < cvl-1)
                this.nrm[i].add2(
                    -(this.cv[i+1].y - this.cv[i].y),
                    this.cv[i+1].x - this.cv[i].x
                );
            this.nrm[i].normalize();
        }
    },
    
    updateBounds: function()
    {
        this.bounds = new Rect2(this.cv[0]);
        for(var i = this.cv.length; --i >= 0;) {
            this.bounds.enclose(this.cv[i].x, this.cv[i].y);
        }
        this.bounds.updateExtent();
    },
    
    
    twig: function(u, style, genops)
    {
        var nu = new Branch({
            upos:   u,
            style:  style
        });
        
        if(style == SPIKE)
            nu.twigRule = this.getMutatedRule(mutate ? 0.15 : 0);
        
        genops.pos = this.uPnt(u);
        genops.angle += Vec2.angle(this.uNrm(u));
        genops.len *= this.bounds.hyp * (1-u);
        
        nu.gen(genops);
        
        // add twig
        this.addSub(nu);
        addBranch(nu);

        return nu;
    },
    
    leaf: function(u, angle)
    {
        var nu = new Leaf(
            this.uPnt(u),
            Vec2.angle(this.uNrm(u)) + angle,
            this.bounds.hyp * (1-u) * rand2(0.2, 0.3)
        );
        
        this.addLeaf(nu);
    },
    
    multiTwig: function()
    {
        var n = Math.floor(this.twigRule.nbr[0]);
        if(branches.length + n < maxBranches) {
            for(var i=this.leaves.length; --i >= 0;)
                this.leaves[i].detach();
            
            var tr = this.twigRule;
            for(var i=0; i < n; i++) {
                var side = Math.round(tr.side[i % tr.side.length]);
                var u = (i + 1) / (n + 1);
                var style = tr.style[i % tr.style.length];//i==flowerIdx ? FLOWER : so.style[i % so.style.length];
                this.twig(u, style, {
                    angle:  side ? tr.angle[i % tr.angle.length] : Math.PI - tr.angle[i % tr.angle.length],
                    crook:  tr.crook[i % tr.crook.length],
                    len:    tr.len[i % tr.len.length],
                    weight: this.weight,
                    ncv:    Math.floor(tr.ncv[i % tr.ncv.length])
                });
            }
            
            this.twigRule = null;
        }
    },
    
    getMutatedRule: function(mutation)
    {
        if(arguments.length == 0)
            mutation = 0;
        
        var rule;
        if(mutation == 0) {
            rule = clone(this.twigRule);
        } else {
            rule = {};
            for(var key in this.twigRule) {
                if(key == "style" || key == "side" || key == "flower") {
                    rule[key] = clone(this.twigRule[key]);
                }
                else {
                    var limits = Branch.ruleLimits[key];
                    rule[key] = [];
                    for(var i=0, rl=this.twigRule[key].length; i < rl; i++) {
                        rule[key].push(clamp(
                            this.twigRule[key][i] + rand2(-mutation,mutation) * (limits[1]-limits[0]),
                            limits[0],
                            limits[1]
                        ));
                    }
                }
            }
        }
        
        rule.flower = false;
        
        return rule;
    },
    
    pollenate: function()
    {
        if(this.twigRule) {
            this.twigRule.flower = true;
        }
    },
    
    
    // remove me from parents and children
    prune: function()
    {
        if(this.parent)
            this.parent.removeSub(this);
        for(var i=this.sub.length; --i >= 0;)
            this.sub[i].parent = null;
        for(var i=this.leaves.length; --i >= 0;)
            this.leaves[i].parent = null;
        this.sub = null;
        this.leaves = null;
    },
    
    
    uPnt: function(u)
    {
        u *= this.cv.length-1;
        var iu = Math.floor(u);
        var fu = u - iu;
        
        if(fu == 0)
            return new Vec2(this.cv[iu].x, this.cv[iu].y);
        
        var b = iu * 3;
        return new Vec2(
            bezierPoint(this.bez[b].x, this.bez[b+1].x, this.bez[b+2].x, this.bez[b+3].x, fu),
            bezierPoint(this.bez[b].y, this.bez[b+1].y, this.bez[b+2].y, this.bez[b+3].y, fu)
        );
    },
    
    uNrm: function(u)
    {
        u *= this.cv.length-1;
        var iu = Math.floor(u);
        var fu = u - iu;
        if(fu == 0)
            return new Vec2(this.nrm[iu].x, this.nrm[iu].y);
        return new Vec2(
            lerp(this.nrm[iu].x, this.nrm[iu+1].x, fu),
            lerp(this.nrm[iu].y, this.nrm[iu+1].y, fu)
        );
    }
};



// BRANCH DISPLAY

Branch.draw_spike = function(br)
{
    if(br.cv.length > 0 && br.uease > 0) {
        var u = br.uease * (br.cv.length-1);
        var uint = Math.floor(u);
        var uf = u - uint;
        
        var w = br.weight * br.bounds.hyp;
        
        var nrmx = [];
        var nrmy = [];
        for(var i=0; i <= uint; i++) {
            var th = Math.max(0, 1 - i/(br.cv.length-1) - (1-br.uease)) * w;
            nrmx.push(br.nrm[i].x * th);
            nrmy.push(br.nrm[i].y * th);
        }
        
        g.noStroke();
        g.fill.apply(g, br.color);
        g.beginPath();
        g.moveTo(br.cv[0].x + nrmx[0], br.cv[0].y + nrmy[0]);
        
        // side A
        for(var i=0; i < uint; i++) {
            var b = i * 3 + 1;
            var th = w * (1-br.uease);
            g.gfx.bezierCurveTo(
                br.bez[b].x   + nrmx[i],   br.bez[b].y   + nrmy[i],
                br.bez[b+1].x + nrmx[i+1], br.bez[b+1].y + nrmy[i+1],
                br.bez[b+2].x + nrmx[i+1], br.bez[b+2].y + nrmy[i+1]
            );
        }
        
        // tip
        if(uf > 0) {
            var b = uint * 3;
            
            var tip = semiBezier(uf,
                br.bez[b].x, br.bez[b].y,
                br.bez[b+1].x, br.bez[b+1].y,
                br.bez[b+2].x, br.bez[b+2].y,
                br.bez[b+3].x, br.bez[b+3].y
            );
            
            g.gfx.bezierCurveTo(
                tip[0] + nrmx[uint], tip[1] + nrmy[uint],
                tip[2], tip[3],
                tip[4], tip[5]
            );
            g.gfx.bezierCurveTo(
                tip[2], tip[3],
                tip[0] - nrmx[uint], tip[1] - nrmy[uint],
                br.bez[b].x - nrmx[uint], br.bez[b].y - nrmy[uint]
            );
        }
        
        // side B
        for(var i=uint; --i >= 0;) {
            var b = i * 3;
            g.gfx.bezierCurveTo(
                br.bez[b+2].x - nrmx[i+1], br.bez[b+2].y - nrmy[i+1],
                br.bez[b+1].x - nrmx[i],   br.bez[b+1].y - nrmy[i],
                br.bez[b].x   - nrmx[i],   br.bez[b].y   - nrmy[i]
            );
        }
        
        // round base
        g.gfx.bezierCurveTo(
            br.bez[0].x - nrmx[0] - nrmy[0], br.bez[0].y - nrmy[0] + nrmx[0],
            br.bez[0].x + nrmx[0] - nrmy[0], br.bez[0].y + nrmy[0] + nrmx[0],
            br.bez[0].x + nrmx[0], br.bez[0].y + nrmy[0]
        );
        
        g.endPath();
    }
};


Branch.ruleLimits = {
    nbr:   [6, 20],
    ncv:   [6, 32],
    angle: [-Math.PI * 0.35, Math.PI * 0.35],
    crook: [0, Math.PI/9],
    side:  [0, 1],
    len:   [0.5, 1.0]
};