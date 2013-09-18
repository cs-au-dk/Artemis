// Just A Grip of Code Compiled From Various Files
// Check http://code.google.com/p/chrome-canopy/source/browse/#svn/trunk/www/js for something more human readable ;)

function lerp(a,b,u)
{return a+(b-a)*u;}
function map(v,in_min,in_max,out_min,out_max)
{return out_min+(out_max-out_min)*((v-in_min)/(in_max-in_min));}
function randInt(max)
{return Math.floor(Math.random()*max);}
function randInt2(min,max)
{return Math.floor(min+Math.random()*(max-min));}
function rand(max)
{return Math.random()*max;}
function rand2(min,max)
{return min+Math.random()*(max-min);}
function clamp(v,min,max)
{return v<min?min:(v>max?max:v);}
function wrap(v,min,max)
{if(v<min)return max-(min-v)%(max-min);else if(v>=max)return(v-min)%(max-min)+min;else return v;}
function distSq(x1,y1,x2,y2)
{var xo=x2-x1;var yo=y2-y1;return xo*xo+yo*yo;}
function dist(x1,y1,x2,y2)
{return Math.sqrt(distSq(x1,y1,x2,y2));}
function rotx(x,angle)
{return x*Math.cos(angle);}
function roty(y,angle)
{return y*Math.sin(angle);}
function bezierPoint(a,b,c,d,t)
{var t1=1.0-t;return a*t1*t1*t1+3*b*t*t1*t1+3*c*t*t*t1+d*t*t*t;}
function segIntersection(p1,p2,p3,p4)
{var bx=p2.x-p1.x;var by=p2.y-p1.y;var dx=p4.x-p3.x;var dy=p4.y-p3.y;var b_dot_d_perp=bx*dy-by*dx;if(b_dot_d_perp==0)return null;var cx=p3.x-p1.x;var cy=p3.y-p1.y;var t=(cx*dy-cy*dx)/b_dot_d_perp;if(t<0||t>1)return null;var u=(cx*by-cy*bx)/b_dot_d_perp;if(u<0||u>1)return null;return new Vec2(p1.x+t*bx,p1.y+t*by);}
function segCircIntersects(l1,l2,cp,cr)
{var u=((cp.x-l1.x)*(l2.x-l1.x)+(cp.y-l1.y)*(l2.y-l1.y))/((l2.x-l1.x)*(l2.x-l1.x)+(l2.y-l1.y)*(l2.y-l1.y));if(u<0)return Vec2.distSq(l1,cp)<cr*cr;if(u>1)return Vec2.distSq(l2,cp)<cr*cr;var ox=l1.x+(l2.x-l1.x)*u-cp.x;var oy=l1.y+(l2.y-l1.y)*u-cp.y;return ox*ox+oy*oy<=cr*cr;}
function curveSegmentBez(v1,v2,v3,v4,s)
{return[new Vec2(v2.x+(s*v3.x-s*v1.x)/6,v2.y+(s*v3.y-s*v1.y)/6),new Vec2(v3.x+(s*v2.x-s*v4.x)/6,v3.y+(s*v2.y-s*v4.y)/6),new Vec2(v3.x,v3.y)];}
function semiBezier(t,x0,y0,x1,y1,x2,y2,x3,y3)
{if(t==0.0){return[x0,y0,x0,y0,x0,y0];}
else if(t==1.0){return[x1,y1,x2,y2,x3,y3];}
var qx1=x0+(x1-x0)*t;var qy1=y0+(y1-y0)*t;var qx2=x1+(x2-x1)*t;var qy2=y1+(y2-y1)*t;var qx3=x2+(x3-x2)*t;var qy3=y2+(y3-y2)*t;var rx2=qx1+(qx2-qx1)*t;var ry2=qy1+(qy2-qy1)*t;var rx3=qx2+(qx3-qx2)*t;var ry3=qy2+(qy3-qy2)*t;var bx3=rx2+(rx3-rx2)*t;var by3=ry2+(ry3-ry2)*t;return[qx1,qy1,rx2,ry2,bx3,by3];}
function clone(obj)
{if(obj==null||typeof(obj)!='object')
return obj;var temp=new obj.constructor();for(var key in obj)
temp[key]=clone(obj[key]);return temp;}
Array.prototype.indexOf=function(elem){for(var i=0;i<this.length;i++)
if(this[i]===elem)
return i;return-1;}
function quadIn(t,b,c,d){return c*(t/=d)*t+b;}
function quadOut(t,b,c,d){return-c*(t/=d)*(t-2)+b;}
function quadInOut(t,b,c,d){if((t/=d/2)<1)
return c/2*t*t+b;return-c/2*((--t)*(t-2)-1)+b;}
function linearNone(t,b,c,d){return c*t/d+b;}
function Vec2(_x,_y)
{this.x=_x;this.y=_y;}
Vec2.prototype={set:function(_x,_y)
{this.x=_x;this.y=_y;},add:function(v)
{this.x+=v.x;this.y+=v.y;},add2:function(_x,_y)
{this.x+=_x;this.y+=_y===undefined?_x:_y;},mul2:function(_x,_y)
{this.x*=_x;this.y*=_y===undefined?_x:_y;},transform:function(origin,mv,sc,rot)
{var xo=(this.x-origin.x+mv.x)*sc;var yo=(this.y-origin.y+mv.y)*sc;if(rot){this.x=origin.x+(xo*Math.cos(rot)-yo*Math.sin(rot));this.y=origin.y+(xo*Math.sin(rot)+yo*Math.cos(rot));}
else{this.x=origin.x+xo;this.y=origin.y+yo;}},normalize:function()
{var m=Math.sqrt(this.x*this.x+this.y*this.y);if(m!=0){this.x/=m;this.y/=m;}},equals:function(v)
{return x==v.x&&y==v.y;}};Vec2.dist=function(v1,v2)
{return Math.sqrt(Vec2.distSq(v1,v2));};Vec2.distSq=function(v1,v2)
{return distSq(v1.x,v1.y,v2.x,v2.y);};Vec2.mag=function(v)
{return Math.sqrt(v.x*v.x+v.y*v.y);};Vec2.angle=function(v)
{return Math.atan2(v.y,v.x);};Vec2.copy=function(v)
{return new Vec2(v.x,v.y);};Vec2.fromAngOff=function(x,y,angle)
{var c=Math.cos(angle);var s=Math.sin(angle);return new Vec2(x*c-y*s,x*s+y*c);};function Rect2(p1,p2)
{this.min=new Vec2(p1.x,p1.y);this.max=p2===undefined?new Vec2(p1.x,p1.y):new Vec2(p2.x,p2.y);this.extent=new Vec2();this.center=new Vec2();this.hyp=0;this.updateExtent();}
Rect2.prototype={draw:function()
{g.rect(this.min.x,this.min.y,this.extent.x,this.extent.y);},enclose:function(x,y)
{if(x<this.min.x)this.min.x=x;if(y<this.min.y)this.min.y=y;if(x>this.max.x)this.max.x=x;if(y>this.max.y)this.max.y=y;},contains:function(x,y)
{return x>this.min.x&&x<this.max.x&&y>this.min.y&&y<this.max.y;},containsRect:function(rect)
{return(rect.min.x>this.min.x&&rect.min.x<this.max.x&&rect.min.y>this.min.y&&rect.min.y<this.max.y&&rect.max.x>this.min.x&&rect.max.x<this.max.x&&rect.max.y>this.min.y&&rect.max.y<this.max.y);},updateExtent:function()
{this.extent.set(this.max.x-this.min.x,this.max.y-this.min.y);this.center.set(this.min.x+this.extent.x/2,this.min.y+this.extent.y/2);this.hyp=Vec2.mag(this.extent);},transform:function(origin,mv,sc)
{this.min.transform(origin,mv,sc);this.max.transform(origin,mv,sc);this.center.transform(origin,mv,sc);this.extent.mul2(sc);this.hyp*=sc;}};Rect2.intersects=function(r1,r2)
{return r1.min.x<r2.max.x&&r1.max.x>r2.min.x&&r1.min.y<r2.max.y&&r1.max.y>r2.min.y;};function Brush(canvas)
{if(typeof canvas=="string")
canvas=document.getElementById(canvas);return buildBrush(canvas);}
function buildBrush(canvas)
{var g={};var gfx=canvas.getContext("2d");g.canvas=canvas;g.gfx=gfx;g.frameRate=30;g.frameCount=0;g.draw=undefined;var doFill=true;var doStroke=true;var loopId=0;var loopStarted=false;var startMillis=(new Date).getTime();g.size=function(_w,_h)
{g.canvas.width=g.width=_w;g.canvas.height=g.height=_h;}
g.loopOn=function(drawFunk)
{if(loopStarted)
clearInterval(loopId);g.draw=drawFunk;loopId=setInterval(function(){try{g.draw();g.frameCount++;}
catch(e){clearInterval(loopId);throw e;}},1000/g.frameRate);loopStarted=true;};g.setFrameRate=function(fps)
{g.frameRate=fps;};g.millis=function()
{return(new Date).getTime()-startMillis;};g.beginPath=function()
{gfx.beginPath();};g.endPath=function()
{if(doFill)
gfx.fill();if(doStroke)
gfx.stroke();gfx.closePath();};g.moveTo=function(x,y)
{gfx.moveTo(x,y);g.lastx=x;g.lasty=y;};g.lineTo=function(x,y)
{gfx.lineTo(x,y);g.lastx=x;g.lasty=y;};g.bezierTo=function(t,x1,y1,x2,y2,x3,y3)
{if(t==1.0){gfx.bezierCurveTo(x1,y1,x2,y2,x3,y3);g.lastx=x3;g.lasty=y3;}
else{var semi=semiBezier(t,g.lastx,g.lasty,x1,y1,x2,y2,x3,y3);gfx.bezierCurveTo.apply(gfx,semi);g.lastx=semi[4];g.lasty=semi[5];}};g.circle=function(x,y,radius)
{g.beginPath();gfx.arc(x,y,radius,0,Math.PI*2,false);g.endPath();};g.rect=function(x,y,w,h)
{g.beginPath();gfx.rect(x,y,width,height);g.endPath();};g.erase=function()
{gfx.clearRect(0,0,g.width,g.height);};g.push=function()
{gfx.save();};g.pop=function()
{gfx.restore();};g.lineWidth=function(w){gfx.lineWidth=w;};g.stroke=function(){doStroke=true;gfx.strokeStyle=g.color.apply(this,arguments)+"";};g.fill=function(){doFill=true;gfx.fillStyle=g.color.apply(this,arguments)+"";};g.noStroke=function(){doStroke=false;};g.noFill=function(){doFill=false;};g.color=function(_r,_g,_b,_a)
{if(arguments.length==2)
_a=_g;else if(arguments.length<4)
_a=255;if(arguments.length<3){_g=_r;_b=_r;}
return"rgba("+_r+","+_g+","+_b+","+(_a/255)+")";};return g;}
function Leaf(pos,rot,len)
{this.pos=pos;this.rot=rot;this.vel=new Vec2(0,0);this.rotvel=0;var l2=len*rand2(0.2,0.3);this.bez=[new Vec2(0,0),new Vec2(len*0.333,l2),new Vec2(len*0.666,l2),new Vec2(len,0),new Vec2(len*0.666,-l2),new Vec2(len*0.333,-l2),new Vec2(0,0)];}
Leaf.prototype={attached:true,udeath:0,update:function()
{if(!this.attached){this.udeath=Math.min(1,(g.millis()-this.detachTime)/this.pruneDelay);if(this.udeath==1){this.prune();}
else{this.pos.add(this.vel);this.rot+=this.rotvel;}}},draw:function(scale)
{if(!this.attached)
scale*=1-this.udeath;g.push();g.gfx.translate(this.pos.x,this.pos.y);g.gfx.rotate(this.rot);g.gfx.scale(scale,scale);g.beginPath();g.gfx.moveTo(this.bez[0].x,this.bez[0].y);g.gfx.bezierCurveTo(this.bez[1].x,this.bez[1].y,this.bez[2].x,this.bez[2].y,this.bez[3].x,this.bez[3].y);g.gfx.bezierCurveTo(this.bez[4].x,this.bez[4].y,this.bez[5].x,this.bez[5].y,this.bez[6].x,this.bez[6].y);g.endPath();g.pop();},transform:function(origin,mv,sc)
{this.pos.transform(origin,mv,sc);this.vel.mul2(sc);for(var i=this.bez.length;--i>=0;)
this.bez[i].mul2(sc);},detach:function()
{var mag=rand2(0.025,0.1);this.vel.set(rotx(this.bez[3].x,this.rot)*mag,roty(this.bez[3].x,this.rot)*mag);this.rotvel=rand2(-0.1,0.1);this.attached=false;this.detachTime=g.millis();this.pruneDelay=randInt2(500,1000);},prune:function()
{if(this.parent)
this.parent.removeLeaf(this);}}
function Branch(ops)
{this.growDur=randInt2(250,750);this.birthTime=g.millis();this.cv=[];this.nrm=[];this.bez=[];this.sub=[];this.leaves=[];if(ops){for(var key in ops){this[key]=ops[key];}}}
Branch.prototype={color:[255,255,255,255],style:SPIKE,ugrow:0,uease:0,finished:false,gen:function(ops)
{this.cv=[];this.weight=ops.weight;var
ncv1=ops.ncv-1,ang=ops.angle,angv=0,cv1=clone(ops.pos),cv2;this.pushCv(cv1);for(var i=0;i<ncv1;i++){cv2=new Vec2(cv1.x+rotx(ops.len/ncv1,ang),cv1.y+roty(ops.len/ncv1,ang));angv+=rand2(-ops.crook,ops.crook);ang+=angv;if(this.style==FLOWER){ang+=wrap(ang+Math.PI*0.5,-Math.PI,Math.PI)*-0.2;}
var is=findIntersection(cv1,cv2);if(is&&i!=0){this.pushCv(is);break;}
else{this.pushCv(cv2);}
cv1=cv2;}
this.bake();if(flower&&flowerMoment&&this.twigRule){var tr=this.twigRule;var n=Math.floor(tr.nbr[0]);for(var i=0;i<n;i++){var side=Math.round(1-tr.side[i%tr.side.length])
this.leaf((i+1)/(n+1),side?tr.angle[i%tr.angle.length]:Math.PI-tr.angle[i%tr.angle.length]);}}},update:function()
{var time=g.millis()-this.birthTime;this.ugrow=time>this.growDur?1:linearNone(time,0,1,this.growDur);this.uease=time>this.growDur?1:quadOut(time,0,1,this.growDur);if(this.parent)
this.ugrow=Math.max(0,this.ugrow-(1-Math.min(1,this.parent.ugrow/this.upos)));if(this.twigRule&&this.sub.length==0&&this.ugrow>=1&&this.bounds.hyp>=minLengthToSpawn&&this.bounds.hyp<viewBounds.hyp){this.multiTwig();}
for(var i=this.leaves.length;--i>=0;)
this.leaves[i].update();},draw:function()
{this.color[3]=Math.min(255,map(this.bounds.hyp,maxLength*0.8,maxLength,255,0));Branch.draw_spike(this);for(var i=this.leaves.length;--i>=0;)
this.leaves[i].draw(this.uease);},pushCv:function(v)
{this.cv.push(v);},popCv:function()
{return this.cv.pop();},addSub:function(br)
{br.parent=this;this.sub.push(br);},removeSub:function(br)
{br.parent=null;var i=this.sub.indexOf(br);if(i>=0)
this.sub.splice(i,1);},addLeaf:function(leaf)
{leaf.parent=this;this.leaves.push(leaf);},removeLeaf:function(leaf)
{leaf.parent=null;var i=this.leaves.indexOf(leaf);if(i>=0)
this.leaves.splice(i,1);},transform:function(origin,mv,sc)
{for(var i=this.cv.length;--i>=0;)
this.cv[i].transform(origin,mv,sc);for(var i=this.bez.length;--i>=0;)
this.bez[i].transform(origin,mv,sc);this.bounds.transform(origin,mv,sc);for(var i=this.leaves.length;--i>=0;)
this.leaves[i].transform(origin,mv,sc);},bake:function()
{this.updateNormals();this.updateBezier();this.updateBounds();},updateBezier:function()
{var s=1;var cvl1=this.cv.length-1;this.bez=[clone(this.cv[0])];this.bez.push.apply(this.bez,curveSegmentBez(this.cv[0],this.cv[0],this.cv[1],this.cv[2],s));for(var i=1;i<cvl1-1;i++){this.bez.push.apply(this.bez,curveSegmentBez(this.cv[i-1],this.cv[i],this.cv[i+1],this.cv[i+2],s));}
this.bez.push.apply(this.bez,curveSegmentBez(this.cv[cvl1-2],this.cv[cvl1-1],this.cv[cvl1],this.cv[cvl1],s));},updateNormals:function()
{this.nrm=[];for(var i=0,cvl=this.cv.length;i<cvl;i++){this.nrm[i]=new Vec2(0,0);if(i>0)
this.nrm[i].add2(-(this.cv[i].y-this.cv[i-1].y),this.cv[i].x-this.cv[i-1].x);if(i<cvl-1)
this.nrm[i].add2(-(this.cv[i+1].y-this.cv[i].y),this.cv[i+1].x-this.cv[i].x);this.nrm[i].normalize();}},updateBounds:function()
{this.bounds=new Rect2(this.cv[0]);for(var i=this.cv.length;--i>=0;){this.bounds.enclose(this.cv[i].x,this.cv[i].y);}
this.bounds.updateExtent();},twig:function(u,style,genops)
{var nu=new Branch({upos:u,style:style});if(style==SPIKE)
nu.twigRule=this.getMutatedRule(mutate?0.15:0);genops.pos=this.uPnt(u);genops.angle+=Vec2.angle(this.uNrm(u));genops.len*=this.bounds.hyp*(1-u);nu.gen(genops);this.addSub(nu);addBranch(nu);return nu;},leaf:function(u,angle)
{var nu=new Leaf(this.uPnt(u),Vec2.angle(this.uNrm(u))+angle,this.bounds.hyp*(1-u)*rand2(0.2,0.3));this.addLeaf(nu);},multiTwig:function()
{var n=Math.floor(this.twigRule.nbr[0]);if(branches.length+n<maxBranches){for(var i=this.leaves.length;--i>=0;)
this.leaves[i].detach();var tr=this.twigRule;for(var i=0;i<n;i++){var side=Math.round(tr.side[i%tr.side.length]);var u=(i+1)/(n+1);var style=tr.style[i%tr.style.length];this.twig(u,style,{angle:side?tr.angle[i%tr.angle.length]:Math.PI-tr.angle[i%tr.angle.length],crook:tr.crook[i%tr.crook.length],len:tr.len[i%tr.len.length],weight:this.weight,ncv:Math.floor(tr.ncv[i%tr.ncv.length])});}
this.twigRule=null;}},getMutatedRule:function(mutation)
{if(arguments.length==0)
mutation=0;var rule;if(mutation==0){rule=clone(this.twigRule);}else{rule={};for(var key in this.twigRule){if(key=="style"||key=="side"||key=="flower"){rule[key]=clone(this.twigRule[key]);}
else{var limits=Branch.ruleLimits[key];rule[key]=[];for(var i=0,rl=this.twigRule[key].length;i<rl;i++){rule[key].push(clamp(this.twigRule[key][i]+rand2(-mutation,mutation)*(limits[1]-limits[0]),limits[0],limits[1]));}}}}
rule.flower=false;return rule;},pollenate:function()
{if(this.twigRule){this.twigRule.flower=true;}},prune:function()
{if(this.parent)
this.parent.removeSub(this);for(var i=this.sub.length;--i>=0;)
this.sub[i].parent=null;for(var i=this.leaves.length;--i>=0;)
this.leaves[i].parent=null;this.sub=null;this.leaves=null;},uPnt:function(u)
{u*=this.cv.length-1;var iu=Math.floor(u);var fu=u-iu;if(fu==0)
return new Vec2(this.cv[iu].x,this.cv[iu].y);var b=iu*3;return new Vec2(bezierPoint(this.bez[b].x,this.bez[b+1].x,this.bez[b+2].x,this.bez[b+3].x,fu),bezierPoint(this.bez[b].y,this.bez[b+1].y,this.bez[b+2].y,this.bez[b+3].y,fu));},uNrm:function(u)
{u*=this.cv.length-1;var iu=Math.floor(u);var fu=u-iu;if(fu==0)
return new Vec2(this.nrm[iu].x,this.nrm[iu].y);return new Vec2(lerp(this.nrm[iu].x,this.nrm[iu+1].x,fu),lerp(this.nrm[iu].y,this.nrm[iu+1].y,fu));}};Branch.draw_spike=function(br)
{if(br.cv.length>0&&br.uease>0){var u=br.uease*(br.cv.length-1);var uint=Math.floor(u);var uf=u-uint;var w=br.weight*br.bounds.hyp;var nrmx=[];var nrmy=[];for(var i=0;i<=uint;i++){var th=Math.max(0,1-i/(br.cv.length-1)-(1-br.uease))*w;nrmx.push(br.nrm[i].x*th);nrmy.push(br.nrm[i].y*th);}
g.noStroke();g.fill.apply(g,br.color);g.beginPath();g.moveTo(br.cv[0].x+nrmx[0],br.cv[0].y+nrmy[0]);for(var i=0;i<uint;i++){var b=i*3+1;var th=w*(1-br.uease);g.gfx.bezierCurveTo(br.bez[b].x+nrmx[i],br.bez[b].y+nrmy[i],br.bez[b+1].x+nrmx[i+1],br.bez[b+1].y+nrmy[i+1],br.bez[b+2].x+nrmx[i+1],br.bez[b+2].y+nrmy[i+1]);}
if(uf>0){var b=uint*3;var tip=semiBezier(uf,br.bez[b].x,br.bez[b].y,br.bez[b+1].x,br.bez[b+1].y,br.bez[b+2].x,br.bez[b+2].y,br.bez[b+3].x,br.bez[b+3].y);g.gfx.bezierCurveTo(tip[0]+nrmx[uint],tip[1]+nrmy[uint],tip[2],tip[3],tip[4],tip[5]);g.gfx.bezierCurveTo(tip[2],tip[3],tip[0]-nrmx[uint],tip[1]-nrmy[uint],br.bez[b].x-nrmx[uint],br.bez[b].y-nrmy[uint]);}
for(var i=uint;--i>=0;){var b=i*3;g.gfx.bezierCurveTo(br.bez[b+2].x-nrmx[i+1],br.bez[b+2].y-nrmy[i+1],br.bez[b+1].x-nrmx[i],br.bez[b+1].y-nrmy[i],br.bez[b].x-nrmx[i],br.bez[b].y-nrmy[i]);}
g.gfx.bezierCurveTo(br.bez[0].x-nrmx[0]-nrmy[0],br.bez[0].y-nrmy[0]+nrmx[0],br.bez[0].x+nrmx[0]-nrmy[0],br.bez[0].y+nrmy[0]+nrmx[0],br.bez[0].x+nrmx[0],br.bez[0].y+nrmy[0]);g.endPath();}};Branch.ruleLimits={nbr:[6,20],ncv:[6,32],angle:[-Math.PI*0.35,Math.PI*0.35],crook:[0,Math.PI/9],side:[0,1],len:[0.5,1.0]};var
canvas,container,g,mouse=new Vec2(0,0),viewBounds,cullBounds,viewBoundsMax=new Vec2(1000,500),root,branches=[],mouseBranch,maxLength,minLengthToSpawn=50,maxBranches=100,origin,zoomVel=0,panVel=0,bgColor=[0,0,0],playing=false,mutate=false,flower=false,aboutOn=false,NONE="none",PAINT="paint",ERASE="erase",SPIKE="spike",STROKE="stroke",FLOWER="flower",paintTool,paintStyle,paintRadius=20,flowerMoment=false,flowerMomentId;window.onload=function justInit()
{$("#my_container").fadeIn(500);canvas=document.getElementById("my_canvas");container=document.getElementById("my_container");$(canvas).bind("mousedown",onMouseDown);$(document).bind("mouseup",onMouseUp);$(document).bind("mousemove",onMouseMove);$(document).bind("keydown",onKeyDown);g=new Brush(canvas);g.setFrameRate(30);g.loopOn(justDraw);sizeToWindow();origin=new Vec2(viewBounds.center.x,viewBounds.center.y);window.onresize=sizeToWindow;set_tool(NONE);set_paint_style(SPIKE);toggle("mutate",false);toggle("flower",false);initRoot();var hash=window.location.hash.substring(1);if(hash=="play")
toggle("play",true);else
toggle("about",true);};function initRoot()
{clearBranches();root=new Branch({style:paintStyle,twigRule:{nbr:[8],ncv:[16,16,16,16],angle:[rand2(-Math.PI,Math.PI)*0.33],crook:[0.1],side:[0,1],style:[SPIKE],len:[1,1,1,1],flower:false}});root.gen({pos:new Vec2(g.width*rand2(0.25,0.75),g.height),angle:-Math.PI/2,crook:0.05,len:g.height,weight:0.04,ncv:16});addBranch(root);}
function sizeToWindow()
{var winw=window.innerWidth;var winh=window.innerHeight;viewBounds=new Rect2(new Vec2(0,0),new Vec2(Math.min(winw,viewBoundsMax.x),Math.min(winh,viewBoundsMax.y)));cullBounds=new Rect2(new Vec2(viewBounds.min.x-50,viewBounds.min.y-50),new Vec2(viewBounds.max.x+50,viewBounds.max.y+50));maxLength=viewBounds.hyp*10;g.size(viewBounds.extent.x,viewBounds.extent.y);container.style.left=winw/2-viewBounds.extent.x/2;container.style.top=winh/2-viewBounds.extent.y/2;}
function justDraw()
{g.erase();g.noFill();g.stroke(0);for(var i=0,brl=branches.length;i<brl;i++){branches[i].update();branches[i].draw();}
if(mouseBranch){mouseBranch.update();mouseBranch.draw();}
sortByClosestToMouse();var closest=branches[0];if(closest){var ccv=closest.cv[Math.floor(closest.cv.length/2)];origin.set(lerp(origin.x,ccv.x,0.25),lerp(origin.y,ccv.y,0.25));}
if(playing&&closest){var move=new Vec2((viewBounds.center.x-origin.x)*panVel,(viewBounds.center.y-origin.y)*panVel);for(var i=branches.length;--i>=0;){branches[i].transform(origin,move,1+zoomVel);}
var speedy=mouse.down&&closest.style!=FLOWER;zoomVel*=0.9;zoomVel+=lerp(0.001,speedy?0.01:0.002,branches.length/maxBranches);panVel*=0.9;panVel+=lerp(0.001,speedy?0.005:0.002,branches.length/maxBranches);}
cullOffscreen();}
function startFlowerMoment()
{if(flowerMoment)
clearTimeout(flowerMomentId);if(playing){flowerMoment=true;flowerMomentId=setTimeout(endFlowerMoment,randInt2(5000,20000));fadeBg(randInt(130),randInt(130),randInt(130),1000);}}
function endFlowerMoment()
{if(flowerMoment){flowerMoment=false;clearTimeout(flowerMomentId);}
if(flower)
flowerMomentId=setTimeout(startFlowerMoment,randInt2(8000,12000));}
function onMouseDown(e)
{mouse.down=true;}
function onMouseMove(e)
{mouse.set(e.pageX-container.offsetLeft,e.pageY-container.offsetTop);}
function onMouseUp(e)
{mouse.down=false;}
function onKeyDown(e)
{switch(String.fromCharCode(e.keyCode).toLowerCase()){case' ':case'p':toggle('play');break;case'n':reset();break;case'm':toggle('mutate');break;case'b':toggle('flower');break;case'a':toggle('about');break;}}
function addBranch(br)
{branches.push(br);}
function removeBranch(br)
{removeBranchByIndex(branches.indexOf(br));}
function removeBranchByIndex(i)
{branches[i].prune();if(i>=0)
branches.splice(i,1);}
function clearBranches()
{for(var i=branches.length;--i>=0;)
branches[i].prune();branches=[];}
function cullOffscreen()
{for(var i=branches.length;--i>=0;){var br=branches[i];if(!Rect2.intersects(cullBounds,br.bounds)||br.bounds.hyp>maxLength){removeBranchByIndex(i);}}}
function findIntersection(p1,p2)
{var bounds=new Rect2(new Vec2(Math.min(p1.x,p2.x),Math.min(p1.y,p2.y)),new Vec2(Math.max(p1.x,p2.x),Math.max(p1.y,p2.y)));for(var i=branches.length;--i>=0;){var br=branches[i];if(Rect2.intersects(bounds,br.bounds)){for(var j=br.cv.length-1;--j>=0;){var is=segIntersection(p1,p2,br.cv[j],br.cv[j+1]);if(is!==null)
return is;}}}
return null;}
function sortByClosestToMouse()
{for(var i=branches.length;--i>=0;){var ctr_cv=branches[i].cv[Math.floor(branches[i].cv.length/2)];branches[i].distToMouse=Vec2.distSq(mouse,ctr_cv);}
branches.sort(sortMouseDist);}
function sortMouseDist(a,b){return b.distToMouse<a.distToMouse&&b.bounds.hyp<viewBounds.hyp?1:-1;}
function toggle(which,state)
{switch(which)
{case"play":if(arguments.length==1)
state=!playing;playing=state;if(playing){if(flower)startFlowerMoment();$("#control a.tool").removeClass("selected");$("#tog_play").text("pause");}
else{playing=false;zoomVel=panVel=0;mouseBranch=null;$("#tog_play").text("play");$("#tool_"+paintTool).addClass("selected");}
break;case"about":if(arguments.length>1){aboutOn=state;}
else{aboutOn=!aboutOn;state=aboutOn;}
var about=$("#about");if(aboutOn){about.css({left:window.innerWidth/2-(about.width()+28)/2,top:window.innerHeight/2-(about.height()+28)/2});$("<div id=\"aboutclear\"></div>").insertBefore(about).one("mousedown",function(){toggle("about",false);play();});about.fadeIn(200);}
else{$("#aboutclear").remove();about.fadeOut(200);}
break;case"mutate":if(arguments.length>1){mutate=state;}
else{mutate=!mutate;state=mutate;}
break;case"flower":if(arguments.length>1){flower=state;}
else{flower=!flower;state=flower;}
if(flower){if(playing)
startFlowerMoment();}
else{endFlowerMoment();}
break;}
if(state)
$("#tog_"+which).addClass("selected");else
$("#tog_"+which).removeClass("selected");return false;}
function play()
{toggle("play",true);}
function pause()
{toggle("play",false);}
function set_tool(tool)
{playing=false;paintTool=tool;$("#control a.tool").removeClass("selected");$("#tool_"+paintTool).addClass("selected");return false;}
function set_paint_style(style)
{playing=false;paintStyle=style;return false;}
function reset()
{pause();initRoot();fadeBg(0,0,0,1000);return false;}
function fadeBg(r,g,b,dur)
{if(fadeBgFading)
clearInterval(fadeBgTimerId);fadeBgFrom=clone(bgColor);fadeBgStart=(new Date).getTime();fadeBgTo=[r,g,b];fadeBgTimerId=setInterval(function(){var time=(new Date).getTime()-fadeBgStart;if(time<dur){for(var i=3;--i>=0;){bgColor[i]=quadOut(time,fadeBgFrom[i],fadeBgTo[i]-fadeBgFrom[i],dur);}}
else{clearInterval(fadeBgTimerId);bgColor=fadeBgTo;}
$(document.body).css("background-color","rgb("+Math.floor(bgColor[0])+","+Math.floor(bgColor[1])+","+Math.floor(bgColor[2])+")");},13);}
var fadeBgTimerId,fadeBgFading,fadeBgFrom,fadeBgTo,fadeBgStart;(function(){var
window=this,undefined,_jQuery=window.jQuery,_$=window.$,jQuery=window.jQuery=window.$=function(selector,context){return new jQuery.fn.init(selector,context);},quickExpr=/^[^<]*(<(.|\s)+>)[^>]*$|^#([\w-]+)$/,isSimple=/^.[^:#\[\.,]*$/;jQuery.fn=jQuery.prototype={init:function(selector,context){selector=selector||document;if(selector.nodeType){this[0]=selector;this.length=1;this.context=selector;return this;}
if(typeof selector==="string"){var match=quickExpr.exec(selector);if(match&&(match[1]||!context)){if(match[1])
selector=jQuery.clean([match[1]],context);else{var elem=document.getElementById(match[3]);if(elem){if(elem.id!=match[3])
return jQuery().find(selector);var ret=jQuery(elem);ret.context=document;ret.selector=selector;return ret;}
selector=[];}}else
return jQuery(context).find(selector);}else if(jQuery.isFunction(selector))
return jQuery(document).ready(selector);if(selector.selector&&selector.context){this.selector=selector.selector;this.context=selector.context;}
return this.setArray(jQuery.makeArray(selector));},selector:"",jquery:"1.3",size:function(){return this.length;},get:function(num){return num===undefined?jQuery.makeArray(this):this[num];},pushStack:function(elems,name,selector){var ret=jQuery(elems);ret.prevObject=this;ret.context=this.context;if(name==="find")
ret.selector=this.selector+(this.selector?" ":"")+selector;else if(name)
ret.selector=this.selector+"."+name+"("+selector+")";return ret;},setArray:function(elems){this.length=0;Array.prototype.push.apply(this,elems);return this;},each:function(callback,args){return jQuery.each(this,callback,args);},index:function(elem){return jQuery.inArray(elem&&elem.jquery?elem[0]:elem,this);},attr:function(name,value,type){var options=name;if(typeof name==="string")
if(value===undefined)
return this[0]&&jQuery[type||"attr"](this[0],name);else{options={};options[name]=value;}
return this.each(function(i){for(name in options)
jQuery.attr(type?this.style:this,name,jQuery.prop(this,options[name],type,i,name));});},css:function(key,value){if((key=='width'||key=='height')&&parseFloat(value)<0)
value=undefined;return this.attr(key,value,"curCSS");},text:function(text){if(typeof text!=="object"&&text!=null)
return this.empty().append((this[0]&&this[0].ownerDocument||document).createTextNode(text));var ret="";jQuery.each(text||this,function(){jQuery.each(this.childNodes,function(){if(this.nodeType!=8)
ret+=this.nodeType!=1?this.nodeValue:jQuery.fn.text([this]);});});return ret;},wrapAll:function(html){if(this[0]){var wrap=jQuery(html,this[0].ownerDocument).clone();if(this[0].parentNode)
wrap.insertBefore(this[0]);wrap.map(function(){var elem=this;while(elem.firstChild)
elem=elem.firstChild;return elem;}).append(this);}
return this;},wrapInner:function(html){return this.each(function(){jQuery(this).contents().wrapAll(html);});},wrap:function(html){return this.each(function(){jQuery(this).wrapAll(html);});},append:function(){return this.domManip(arguments,true,function(elem){if(this.nodeType==1)
this.appendChild(elem);});},prepend:function(){return this.domManip(arguments,true,function(elem){if(this.nodeType==1)
this.insertBefore(elem,this.firstChild);});},before:function(){return this.domManip(arguments,false,function(elem){this.parentNode.insertBefore(elem,this);});},after:function(){return this.domManip(arguments,false,function(elem){this.parentNode.insertBefore(elem,this.nextSibling);});},end:function(){return this.prevObject||jQuery([]);},push:[].push,find:function(selector){if(this.length===1&&!/,/.test(selector)){var ret=this.pushStack([],"find",selector);ret.length=0;jQuery.find(selector,this[0],ret);return ret;}else{var elems=jQuery.map(this,function(elem){return jQuery.find(selector,elem);});return this.pushStack(/[^+>] [^+>]/.test(selector)?jQuery.unique(elems):elems,"find",selector);}},clone:function(events){var ret=this.map(function(){if(!jQuery.support.noCloneEvent&&!jQuery.isXMLDoc(this)){var clone=this.cloneNode(true),container=document.createElement("div");container.appendChild(clone);return jQuery.clean([container.innerHTML])[0];}else
return this.cloneNode(true);});var clone=ret.find("*").andSelf().each(function(){if(this[expando]!==undefined)
this[expando]=null;});if(events===true)
this.find("*").andSelf().each(function(i){if(this.nodeType==3)
return;var events=jQuery.data(this,"events");for(var type in events)
for(var handler in events[type])
jQuery.event.add(clone[i],type,events[type][handler],events[type][handler].data);});return ret;},filter:function(selector){return this.pushStack(jQuery.isFunction(selector)&&jQuery.grep(this,function(elem,i){return selector.call(elem,i);})||jQuery.multiFilter(selector,jQuery.grep(this,function(elem){return elem.nodeType===1;})),"filter",selector);},closest:function(selector){var pos=jQuery.expr.match.POS.test(selector)?jQuery(selector):null;return this.map(function(){var cur=this;while(cur&&cur.ownerDocument){if(pos?pos.index(cur)>-1:jQuery(cur).is(selector))
return cur;cur=cur.parentNode;}});},not:function(selector){if(typeof selector==="string")
if(isSimple.test(selector))
return this.pushStack(jQuery.multiFilter(selector,this,true),"not",selector);else
selector=jQuery.multiFilter(selector,this);var isArrayLike=selector.length&&selector[selector.length-1]!==undefined&&!selector.nodeType;return this.filter(function(){return isArrayLike?jQuery.inArray(this,selector)<0:this!=selector;});},add:function(selector){return this.pushStack(jQuery.unique(jQuery.merge(this.get(),typeof selector==="string"?jQuery(selector):jQuery.makeArray(selector))));},is:function(selector){return!!selector&&jQuery.multiFilter(selector,this).length>0;},hasClass:function(selector){return!!selector&&this.is("."+selector);},val:function(value){if(value===undefined){var elem=this[0];if(elem){if(jQuery.nodeName(elem,'option'))
return(elem.attributes.value||{}).specified?elem.value:elem.text;if(jQuery.nodeName(elem,"select")){var index=elem.selectedIndex,values=[],options=elem.options,one=elem.type=="select-one";if(index<0)
return null;for(var i=one?index:0,max=one?index+1:options.length;i<max;i++){var option=options[i];if(option.selected){value=jQuery(option).val();if(one)
return value;values.push(value);}}
return values;}
return(elem.value||"").replace(/\r/g,"");}
return undefined;}
if(typeof value==="number")
value+='';return this.each(function(){if(this.nodeType!=1)
return;if(jQuery.isArray(value)&&/radio|checkbox/.test(this.type))
this.checked=(jQuery.inArray(this.value,value)>=0||jQuery.inArray(this.name,value)>=0);else if(jQuery.nodeName(this,"select")){var values=jQuery.makeArray(value);jQuery("option",this).each(function(){this.selected=(jQuery.inArray(this.value,values)>=0||jQuery.inArray(this.text,values)>=0);});if(!values.length)
this.selectedIndex=-1;}else
this.value=value;});},html:function(value){return value===undefined?(this[0]?this[0].innerHTML:null):this.empty().append(value);},replaceWith:function(value){return this.after(value).remove();},eq:function(i){return this.slice(i,+i+1);},slice:function(){return this.pushStack(Array.prototype.slice.apply(this,arguments),"slice",Array.prototype.slice.call(arguments).join(","));},map:function(callback){return this.pushStack(jQuery.map(this,function(elem,i){return callback.call(elem,i,elem);}));},andSelf:function(){return this.add(this.prevObject);},domManip:function(args,table,callback){if(this[0]){var fragment=(this[0].ownerDocument||this[0]).createDocumentFragment(),scripts=jQuery.clean(args,(this[0].ownerDocument||this[0]),fragment),first=fragment.firstChild,extra=this.length>1?fragment.cloneNode(true):fragment;if(first)
for(var i=0,l=this.length;i<l;i++)
callback.call(root(this[i],first),i>0?extra.cloneNode(true):fragment);if(scripts)
jQuery.each(scripts,evalScript);}
return this;function root(elem,cur){return table&&jQuery.nodeName(elem,"table")&&jQuery.nodeName(cur,"tr")?(elem.getElementsByTagName("tbody")[0]||elem.appendChild(elem.ownerDocument.createElement("tbody"))):elem;}}};jQuery.fn.init.prototype=jQuery.fn;function evalScript(i,elem){if(elem.src)
jQuery.ajax({url:elem.src,async:false,dataType:"script"});else
jQuery.globalEval(elem.text||elem.textContent||elem.innerHTML||"");if(elem.parentNode)
elem.parentNode.removeChild(elem);}
function now(){return+new Date;}
jQuery.extend=jQuery.fn.extend=function(){var target=arguments[0]||{},i=1,length=arguments.length,deep=false,options;if(typeof target==="boolean"){deep=target;target=arguments[1]||{};i=2;}
if(typeof target!=="object"&&!jQuery.isFunction(target))
target={};if(length==i){target=this;--i;}
for(;i<length;i++)
if((options=arguments[i])!=null)
for(var name in options){var src=target[name],copy=options[name];if(target===copy)
continue;if(deep&&copy&&typeof copy==="object"&&!copy.nodeType)
target[name]=jQuery.extend(deep,src||(copy.length!=null?[]:{}),copy);else if(copy!==undefined)
target[name]=copy;}
return target;};var exclude=/z-?index|font-?weight|opacity|zoom|line-?height/i,defaultView=document.defaultView||{},toString=Object.prototype.toString;jQuery.extend({noConflict:function(deep){window.$=_$;if(deep)
window.jQuery=_jQuery;return jQuery;},isFunction:function(obj){return toString.call(obj)==="[object Function]";},isArray:function(obj){return toString.call(obj)==="[object Array]";},isXMLDoc:function(elem){return elem.documentElement&&!elem.body||elem.tagName&&elem.ownerDocument&&!elem.ownerDocument.body;},globalEval:function(data){data=jQuery.trim(data);if(data){var head=document.getElementsByTagName("head")[0]||document.documentElement,script=document.createElement("script");script.type="text/javascript";if(jQuery.support.scriptEval)
script.appendChild(document.createTextNode(data));else
script.text=data;head.insertBefore(script,head.firstChild);head.removeChild(script);}},nodeName:function(elem,name){return elem.nodeName&&elem.nodeName.toUpperCase()==name.toUpperCase();},each:function(object,callback,args){var name,i=0,length=object.length;if(args){if(length===undefined){for(name in object)
if(callback.apply(object[name],args)===false)
break;}else
for(;i<length;)
if(callback.apply(object[i++],args)===false)
break;}else{if(length===undefined){for(name in object)
if(callback.call(object[name],name,object[name])===false)
break;}else
for(var value=object[0];i<length&&callback.call(value,i,value)!==false;value=object[++i]){}}
return object;},prop:function(elem,value,type,i,name){if(jQuery.isFunction(value))
value=value.call(elem,i);return typeof value==="number"&&type=="curCSS"&&!exclude.test(name)?value+"px":value;},className:{add:function(elem,classNames){jQuery.each((classNames||"").split(/\s+/),function(i,className){if(elem.nodeType==1&&!jQuery.className.has(elem.className,className))
elem.className+=(elem.className?" ":"")+className;});},remove:function(elem,classNames){if(elem.nodeType==1)
elem.className=classNames!==undefined?jQuery.grep(elem.className.split(/\s+/),function(className){return!jQuery.className.has(classNames,className);}).join(" "):"";},has:function(elem,className){return jQuery.inArray(className,(elem.className||elem).toString().split(/\s+/))>-1;}},swap:function(elem,options,callback){var old={};for(var name in options){old[name]=elem.style[name];elem.style[name]=options[name];}
callback.call(elem);for(var name in options)
elem.style[name]=old[name];},css:function(elem,name,force){if(name=="width"||name=="height"){var val,props={position:"absolute",visibility:"hidden",display:"block"},which=name=="width"?["Left","Right"]:["Top","Bottom"];function getWH(){val=name=="width"?elem.offsetWidth:elem.offsetHeight;var padding=0,border=0;jQuery.each(which,function(){padding+=parseFloat(jQuery.curCSS(elem,"padding"+this,true))||0;border+=parseFloat(jQuery.curCSS(elem,"border"+this+"Width",true))||0;});val-=Math.round(padding+border);}
if(jQuery(elem).is(":visible"))
getWH();else
jQuery.swap(elem,props,getWH);return Math.max(0,val);}
return jQuery.curCSS(elem,name,force);},curCSS:function(elem,name,force){var ret,style=elem.style;if(name=="opacity"&&!jQuery.support.opacity){ret=jQuery.attr(style,"opacity");return ret==""?"1":ret;}
if(name.match(/float/i))
name=styleFloat;if(!force&&style&&style[name])
ret=style[name];else if(defaultView.getComputedStyle){if(name.match(/float/i))
name="float";name=name.replace(/([A-Z])/g,"-$1").toLowerCase();var computedStyle=defaultView.getComputedStyle(elem,null);if(computedStyle)
ret=computedStyle.getPropertyValue(name);if(name=="opacity"&&ret=="")
ret="1";}else if(elem.currentStyle){var camelCase=name.replace(/\-(\w)/g,function(all,letter){return letter.toUpperCase();});ret=elem.currentStyle[name]||elem.currentStyle[camelCase];if(!/^\d+(px)?$/i.test(ret)&&/^\d/.test(ret)){var left=style.left,rsLeft=elem.runtimeStyle.left;elem.runtimeStyle.left=elem.currentStyle.left;style.left=ret||0;ret=style.pixelLeft+"px";style.left=left;elem.runtimeStyle.left=rsLeft;}}
return ret;},clean:function(elems,context,fragment){context=context||document;if(typeof context.createElement==="undefined")
context=context.ownerDocument||context[0]&&context[0].ownerDocument||document;if(!fragment&&elems.length===1&&typeof elems[0]==="string"){var match=/^<(\w+)\s*\/?>$/.exec(elems[0]);if(match)
return[context.createElement(match[1])];}
var ret=[],scripts=[],div=context.createElement("div");jQuery.each(elems,function(i,elem){if(typeof elem==="number")
elem+='';if(!elem)
return;if(typeof elem==="string"){elem=elem.replace(/(<(\w+)[^>]*?)\/>/g,function(all,front,tag){return tag.match(/^(abbr|br|col|img|input|link|meta|param|hr|area|embed)$/i)?all:front+"></"+tag+">";});var tags=jQuery.trim(elem).toLowerCase();var wrap=!tags.indexOf("<opt")&&[1,"<select multiple='multiple'>","</select>"]||!tags.indexOf("<leg")&&[1,"<fieldset>","</fieldset>"]||tags.match(/^<(thead|tbody|tfoot|colg|cap)/)&&[1,"<table>","</table>"]||!tags.indexOf("<tr")&&[2,"<table><tbody>","</tbody></table>"]||(!tags.indexOf("<td")||!tags.indexOf("<th"))&&[3,"<table><tbody><tr>","</tr></tbody></table>"]||!tags.indexOf("<col")&&[2,"<table><tbody></tbody><colgroup>","</colgroup></table>"]||!jQuery.support.htmlSerialize&&[1,"div<div>","</div>"]||[0,"",""];div.innerHTML=wrap[1]+elem+wrap[2];while(wrap[0]--)
div=div.lastChild;if(!jQuery.support.tbody){var tbody=!tags.indexOf("<table")&&tags.indexOf("<tbody")<0?div.firstChild&&div.firstChild.childNodes:wrap[1]=="<table>"&&tags.indexOf("<tbody")<0?div.childNodes:[];for(var j=tbody.length-1;j>=0;--j)
if(jQuery.nodeName(tbody[j],"tbody")&&!tbody[j].childNodes.length)
tbody[j].parentNode.removeChild(tbody[j]);}
if(!jQuery.support.leadingWhitespace&&/^\s/.test(elem))
div.insertBefore(context.createTextNode(elem.match(/^\s*/)[0]),div.firstChild);elem=jQuery.makeArray(div.childNodes);}
if(elem.nodeType)
ret.push(elem);else
ret=jQuery.merge(ret,elem);});if(fragment){for(var i=0;ret[i];i++){if(jQuery.nodeName(ret[i],"script")&&(!ret[i].type||ret[i].type.toLowerCase()==="text/javascript")){scripts.push(ret[i].parentNode?ret[i].parentNode.removeChild(ret[i]):ret[i]);}else{if(ret[i].nodeType===1)
ret.splice.apply(ret,[i+1,0].concat(jQuery.makeArray(ret[i].getElementsByTagName("script"))));fragment.appendChild(ret[i]);}}
return scripts;}
return ret;},attr:function(elem,name,value){if(!elem||elem.nodeType==3||elem.nodeType==8)
return undefined;var notxml=!jQuery.isXMLDoc(elem),set=value!==undefined;name=notxml&&jQuery.props[name]||name;if(elem.tagName){var special=/href|src|style/.test(name);if(name=="selected"&&elem.parentNode)
elem.parentNode.selectedIndex;if(name in elem&&notxml&&!special){if(set){if(name=="type"&&jQuery.nodeName(elem,"input")&&elem.parentNode)
throw"type property can't be changed";elem[name]=value;}
if(jQuery.nodeName(elem,"form")&&elem.getAttributeNode(name))
return elem.getAttributeNode(name).nodeValue;if(name=="tabIndex"){var attributeNode=elem.getAttributeNode("tabIndex");return attributeNode&&attributeNode.specified?attributeNode.value:elem.nodeName.match(/^(a|area|button|input|object|select|textarea)$/i)?0:undefined;}
return elem[name];}
if(!jQuery.support.style&&notxml&&name=="style")
return jQuery.attr(elem.style,"cssText",value);if(set)
elem.setAttribute(name,""+value);var attr=!jQuery.support.hrefNormalized&&notxml&&special?elem.getAttribute(name,2):elem.getAttribute(name);return attr===null?undefined:attr;}
if(!jQuery.support.opacity&&name=="opacity"){if(set){elem.zoom=1;elem.filter=(elem.filter||"").replace(/alpha\([^)]*\)/,"")+
(parseInt(value)+''=="NaN"?"":"alpha(opacity="+value*100+")");}
return elem.filter&&elem.filter.indexOf("opacity=")>=0?(parseFloat(elem.filter.match(/opacity=([^)]*)/)[1])/100)+'':"";}
name=name.replace(/-([a-z])/ig,function(all,letter){return letter.toUpperCase();});if(set)
elem[name]=value;return elem[name];},trim:function(text){return(text||"").replace(/^\s+|\s+$/g,"");},makeArray:function(array){var ret=[];if(array!=null){var i=array.length;if(i==null||typeof array==="string"||jQuery.isFunction(array)||array.setInterval)
ret[0]=array;else
while(i)
ret[--i]=array[i];}
return ret;},inArray:function(elem,array){for(var i=0,length=array.length;i<length;i++)
if(array[i]===elem)
return i;return-1;},merge:function(first,second){var i=0,elem,pos=first.length;if(!jQuery.support.getAll){while((elem=second[i++])!=null)
if(elem.nodeType!=8)
first[pos++]=elem;}else
while((elem=second[i++])!=null)
first[pos++]=elem;return first;},unique:function(array){var ret=[],done={};try{for(var i=0,length=array.length;i<length;i++){var id=jQuery.data(array[i]);if(!done[id]){done[id]=true;ret.push(array[i]);}}}catch(e){ret=array;}
return ret;},grep:function(elems,callback,inv){var ret=[];for(var i=0,length=elems.length;i<length;i++)
if(!inv!=!callback(elems[i],i))
ret.push(elems[i]);return ret;},map:function(elems,callback){var ret=[];for(var i=0,length=elems.length;i<length;i++){var value=callback(elems[i],i);if(value!=null)
ret[ret.length]=value;}
return ret.concat.apply([],ret);}});var userAgent=navigator.userAgent.toLowerCase();jQuery.browser={version:(userAgent.match(/.+(?:rv|it|ra|ie)[\/: ]([\d.]+)/)||[0,'0'])[1],safari:/webkit/.test(userAgent),opera:/opera/.test(userAgent),msie:/msie/.test(userAgent)&&!/opera/.test(userAgent),mozilla:/mozilla/.test(userAgent)&&!/(compatible|webkit)/.test(userAgent)};jQuery.each({parent:function(elem){return elem.parentNode;},parents:function(elem){return jQuery.dir(elem,"parentNode");},next:function(elem){return jQuery.nth(elem,2,"nextSibling");},prev:function(elem){return jQuery.nth(elem,2,"previousSibling");},nextAll:function(elem){return jQuery.dir(elem,"nextSibling");},prevAll:function(elem){return jQuery.dir(elem,"previousSibling");},siblings:function(elem){return jQuery.sibling(elem.parentNode.firstChild,elem);},children:function(elem){return jQuery.sibling(elem.firstChild);},contents:function(elem){return jQuery.nodeName(elem,"iframe")?elem.contentDocument||elem.contentWindow.document:jQuery.makeArray(elem.childNodes);}},function(name,fn){jQuery.fn[name]=function(selector){var ret=jQuery.map(this,fn);if(selector&&typeof selector=="string")
ret=jQuery.multiFilter(selector,ret);return this.pushStack(jQuery.unique(ret),name,selector);};});jQuery.each({appendTo:"append",prependTo:"prepend",insertBefore:"before",insertAfter:"after",replaceAll:"replaceWith"},function(name,original){jQuery.fn[name]=function(){var args=arguments;return this.each(function(){for(var i=0,length=args.length;i<length;i++)
jQuery(args[i])[original](this);});};});jQuery.each({removeAttr:function(name){jQuery.attr(this,name,"");if(this.nodeType==1)
this.removeAttribute(name);},addClass:function(classNames){jQuery.className.add(this,classNames);},removeClass:function(classNames){jQuery.className.remove(this,classNames);},toggleClass:function(classNames,state){if(typeof state!=="boolean")
state=!jQuery.className.has(this,classNames);jQuery.className[state?"add":"remove"](this,classNames);},remove:function(selector){if(!selector||jQuery.filter(selector,[this]).length){jQuery("*",this).add([this]).each(function(){jQuery.event.remove(this);jQuery.removeData(this);});if(this.parentNode)
this.parentNode.removeChild(this);}},empty:function(){jQuery(">*",this).remove();while(this.firstChild)
this.removeChild(this.firstChild);}},function(name,fn){jQuery.fn[name]=function(){return this.each(fn,arguments);};});function num(elem,prop){return elem[0]&&parseInt(jQuery.curCSS(elem[0],prop,true),10)||0;}
var expando="jQuery"+now(),uuid=0,windowData={};jQuery.extend({cache:{},data:function(elem,name,data){elem=elem==window?windowData:elem;var id=elem[expando];if(!id)
id=elem[expando]=++uuid;if(name&&!jQuery.cache[id])
jQuery.cache[id]={};if(data!==undefined)
jQuery.cache[id][name]=data;return name?jQuery.cache[id][name]:id;},removeData:function(elem,name){elem=elem==window?windowData:elem;var id=elem[expando];if(name){if(jQuery.cache[id]){delete jQuery.cache[id][name];name="";for(name in jQuery.cache[id])
break;if(!name)
jQuery.removeData(elem);}}else{try{delete elem[expando];}catch(e){if(elem.removeAttribute)
elem.removeAttribute(expando);}
delete jQuery.cache[id];}},queue:function(elem,type,data){if(elem){type=(type||"fx")+"queue";var q=jQuery.data(elem,type);if(!q||jQuery.isArray(data))
q=jQuery.data(elem,type,jQuery.makeArray(data));else if(data)
q.push(data);}
return q;},dequeue:function(elem,type){var queue=jQuery.queue(elem,type),fn=queue.shift();if(!type||type==="fx")
fn=queue[0];if(fn!==undefined)
fn.call(elem);}});jQuery.fn.extend({data:function(key,value){var parts=key.split(".");parts[1]=parts[1]?"."+parts[1]:"";if(value===undefined){var data=this.triggerHandler("getData"+parts[1]+"!",[parts[0]]);if(data===undefined&&this.length)
data=jQuery.data(this[0],key);return data===undefined&&parts[1]?this.data(parts[0]):data;}else
return this.trigger("setData"+parts[1]+"!",[parts[0],value]).each(function(){jQuery.data(this,key,value);});},removeData:function(key){return this.each(function(){jQuery.removeData(this,key);});},queue:function(type,data){if(typeof type!=="string"){data=type;type="fx";}
if(data===undefined)
return jQuery.queue(this[0],type);return this.each(function(){var queue=jQuery.queue(this,type,data);if(type=="fx"&&queue.length==1)
queue[0].call(this);});},dequeue:function(type){return this.each(function(){jQuery.dequeue(this,type);});}});(function(){var chunker=/((?:\((?:\([^()]+\)|[^()]+)+\)|\[(?:\[[^[\]]*\]|[^[\]]+)+\]|\\.|[^ >+~,(\[]+)+|[>+~])(\s*,\s*)?/g,done=0,toString=Object.prototype.toString;var Sizzle=function(selector,context,results,seed){results=results||[];context=context||document;if(context.nodeType!==1&&context.nodeType!==9)
return[];if(!selector||typeof selector!=="string"){return results;}
var parts=[],m,set,checkSet,check,mode,extra,prune=true;chunker.lastIndex=0;while((m=chunker.exec(selector))!==null){parts.push(m[1]);if(m[2]){extra=RegExp.rightContext;break;}}
if(parts.length>1&&Expr.match.POS.exec(selector)){if(parts.length===2&&Expr.relative[parts[0]]){var later="",match;while((match=Expr.match.POS.exec(selector))){later+=match[0];selector=selector.replace(Expr.match.POS,"");}
set=Sizzle.filter(later,Sizzle(/\s$/.test(selector)?selector+"*":selector,context));}else{set=Expr.relative[parts[0]]?[context]:Sizzle(parts.shift(),context);while(parts.length){var tmpSet=[];selector=parts.shift();if(Expr.relative[selector])
selector+=parts.shift();for(var i=0,l=set.length;i<l;i++){Sizzle(selector,set[i],tmpSet);}
set=tmpSet;}}}else{var ret=seed?{expr:parts.pop(),set:makeArray(seed)}:Sizzle.find(parts.pop(),parts.length===1&&context.parentNode?context.parentNode:context);set=Sizzle.filter(ret.expr,ret.set);if(parts.length>0){checkSet=makeArray(set);}else{prune=false;}
while(parts.length){var cur=parts.pop(),pop=cur;if(!Expr.relative[cur]){cur="";}else{pop=parts.pop();}
if(pop==null){pop=context;}
Expr.relative[cur](checkSet,pop,isXML(context));}}
if(!checkSet){checkSet=set;}
if(!checkSet){throw"Syntax error, unrecognized expression: "+(cur||selector);}
if(toString.call(checkSet)==="[object Array]"){if(!prune){results.push.apply(results,checkSet);}else if(context.nodeType===1){for(var i=0;checkSet[i]!=null;i++){if(checkSet[i]&&(checkSet[i]===true||checkSet[i].nodeType===1&&contains(context,checkSet[i]))){results.push(set[i]);}}}else{for(var i=0;checkSet[i]!=null;i++){if(checkSet[i]&&checkSet[i].nodeType===1){results.push(set[i]);}}}}else{makeArray(checkSet,results);}
if(extra){Sizzle(extra,context,results,seed);}
return results;};Sizzle.matches=function(expr,set){return Sizzle(expr,null,null,set);};Sizzle.find=function(expr,context){var set,match;if(!expr){return[];}
for(var i=0,l=Expr.order.length;i<l;i++){var type=Expr.order[i],match;if((match=Expr.match[type].exec(expr))){var left=RegExp.leftContext;if(left.substr(left.length-1)!=="\\"){match[1]=(match[1]||"").replace(/\\/g,"");set=Expr.find[type](match,context);if(set!=null){expr=expr.replace(Expr.match[type],"");break;}}}}
if(!set){set=context.getElementsByTagName("*");}
return{set:set,expr:expr};};Sizzle.filter=function(expr,set,inplace,not){var old=expr,result=[],curLoop=set,match,anyFound;while(expr&&set.length){for(var type in Expr.filter){if((match=Expr.match[type].exec(expr))!=null){var filter=Expr.filter[type],goodArray=null,goodPos=0,found,item;anyFound=false;if(curLoop==result){result=[];}
if(Expr.preFilter[type]){match=Expr.preFilter[type](match,curLoop,inplace,result,not);if(!match){anyFound=found=true;}else if(match===true){continue;}else if(match[0]===true){goodArray=[];var last=null,elem;for(var i=0;(elem=curLoop[i])!==undefined;i++){if(elem&&last!==elem){goodArray.push(elem);last=elem;}}}}
if(match){for(var i=0;(item=curLoop[i])!==undefined;i++){if(item){if(goodArray&&item!=goodArray[goodPos]){goodPos++;}
found=filter(item,match,goodPos,goodArray);var pass=not^!!found;if(inplace&&found!=null){if(pass){anyFound=true;}else{curLoop[i]=false;}}else if(pass){result.push(item);anyFound=true;}}}}
if(found!==undefined){if(!inplace){curLoop=result;}
expr=expr.replace(Expr.match[type],"");if(!anyFound){return[];}
break;}}}
expr=expr.replace(/\s*,\s*/,"");if(expr==old){if(anyFound==null){throw"Syntax error, unrecognized expression: "+expr;}else{break;}}
old=expr;}
return curLoop;};var Expr=Sizzle.selectors={order:["ID","NAME","TAG"],match:{ID:/#((?:[\w\u00c0-\uFFFF_-]|\\.)+)/,CLASS:/\.((?:[\w\u00c0-\uFFFF_-]|\\.)+)/,NAME:/\[name=['"]*((?:[\w\u00c0-\uFFFF_-]|\\.)+)['"]*\]/,ATTR:/\[\s*((?:[\w\u00c0-\uFFFF_-]|\\.)+)\s*(?:(\S?=)\s*(['"]*)(.*?)\3|)\s*\]/,TAG:/^((?:[\w\u00c0-\uFFFF\*_-]|\\.)+)/,CHILD:/:(only|nth|last|first)-child(?:\((even|odd|[\dn+-]*)\))?/,POS:/:(nth|eq|gt|lt|first|last|even|odd)(?:\((\d*)\))?(?=[^-]|$)/,PSEUDO:/:((?:[\w\u00c0-\uFFFF_-]|\\.)+)(?:\((['"]*)((?:\([^\)]+\)|[^\2\(\)]*)+)\2\))?/},attrMap:{"class":"className","for":"htmlFor"},attrHandle:{href:function(elem){return elem.getAttribute("href");}},relative:{"+":function(checkSet,part){for(var i=0,l=checkSet.length;i<l;i++){var elem=checkSet[i];if(elem){var cur=elem.previousSibling;while(cur&&cur.nodeType!==1){cur=cur.previousSibling;}
checkSet[i]=typeof part==="string"?cur||false:cur===part;}}
if(typeof part==="string"){Sizzle.filter(part,checkSet,true);}},">":function(checkSet,part,isXML){if(typeof part==="string"&&!/\W/.test(part)){part=isXML?part:part.toUpperCase();for(var i=0,l=checkSet.length;i<l;i++){var elem=checkSet[i];if(elem){var parent=elem.parentNode;checkSet[i]=parent.nodeName===part?parent:false;}}}else{for(var i=0,l=checkSet.length;i<l;i++){var elem=checkSet[i];if(elem){checkSet[i]=typeof part==="string"?elem.parentNode:elem.parentNode===part;}}
if(typeof part==="string"){Sizzle.filter(part,checkSet,true);}}},"":function(checkSet,part,isXML){var doneName="done"+(done++),checkFn=dirCheck;if(!part.match(/\W/)){var nodeCheck=part=isXML?part:part.toUpperCase();checkFn=dirNodeCheck;}
checkFn("parentNode",part,doneName,checkSet,nodeCheck,isXML);},"~":function(checkSet,part,isXML){var doneName="done"+(done++),checkFn=dirCheck;if(typeof part==="string"&&!part.match(/\W/)){var nodeCheck=part=isXML?part:part.toUpperCase();checkFn=dirNodeCheck;}
checkFn("previousSibling",part,doneName,checkSet,nodeCheck,isXML);}},find:{ID:function(match,context){if(context.getElementById){var m=context.getElementById(match[1]);return m?[m]:[];}},NAME:function(match,context){return context.getElementsByName?context.getElementsByName(match[1]):null;},TAG:function(match,context){return context.getElementsByTagName(match[1]);}},preFilter:{CLASS:function(match,curLoop,inplace,result,not){match=" "+match[1].replace(/\\/g,"")+" ";for(var i=0;curLoop[i];i++){if(not^(" "+curLoop[i].className+" ").indexOf(match)>=0){if(!inplace)
result.push(curLoop[i]);}else if(inplace){curLoop[i]=false;}}
return false;},ID:function(match){return match[1].replace(/\\/g,"");},TAG:function(match,curLoop){for(var i=0;!curLoop[i];i++){}
return isXML(curLoop[i])?match[1]:match[1].toUpperCase();},CHILD:function(match){if(match[1]=="nth"){var test=/(-?)(\d*)n((?:\+|-)?\d*)/.exec(match[2]=="even"&&"2n"||match[2]=="odd"&&"2n+1"||!/\D/.test(match[2])&&"0n+"+match[2]||match[2]);match[2]=(test[1]+(test[2]||1))-0;match[3]=test[3]-0;}
match[0]="done"+(done++);return match;},ATTR:function(match){var name=match[1];if(Expr.attrMap[name]){match[1]=Expr.attrMap[name];}
if(match[2]==="~="){match[4]=" "+match[4]+" ";}
return match;},PSEUDO:function(match,curLoop,inplace,result,not){if(match[1]==="not"){if(match[3].match(chunker).length>1){match[3]=Sizzle(match[3],null,null,curLoop);}else{var ret=Sizzle.filter(match[3],curLoop,inplace,true^not);if(!inplace){result.push.apply(result,ret);}
return false;}}else if(Expr.match.POS.test(match[0])){return true;}
return match;},POS:function(match){match.unshift(true);return match;}},filters:{enabled:function(elem){return elem.disabled===false&&elem.type!=="hidden";},disabled:function(elem){return elem.disabled===true;},checked:function(elem){return elem.checked===true;},selected:function(elem){elem.parentNode.selectedIndex;return elem.selected===true;},parent:function(elem){return!!elem.firstChild;},empty:function(elem){return!elem.firstChild;},has:function(elem,i,match){return!!Sizzle(match[3],elem).length;},header:function(elem){return/h\d/i.test(elem.nodeName);},text:function(elem){return"text"===elem.type;},radio:function(elem){return"radio"===elem.type;},checkbox:function(elem){return"checkbox"===elem.type;},file:function(elem){return"file"===elem.type;},password:function(elem){return"password"===elem.type;},submit:function(elem){return"submit"===elem.type;},image:function(elem){return"image"===elem.type;},reset:function(elem){return"reset"===elem.type;},button:function(elem){return"button"===elem.type||elem.nodeName.toUpperCase()==="BUTTON";},input:function(elem){return/input|select|textarea|button/i.test(elem.nodeName);}},setFilters:{first:function(elem,i){return i===0;},last:function(elem,i,match,array){return i===array.length-1;},even:function(elem,i){return i%2===0;},odd:function(elem,i){return i%2===1;},lt:function(elem,i,match){return i<match[3]-0;},gt:function(elem,i,match){return i>match[3]-0;},nth:function(elem,i,match){return match[3]-0==i;},eq:function(elem,i,match){return match[3]-0==i;}},filter:{CHILD:function(elem,match){var type=match[1],parent=elem.parentNode;var doneName="child"+parent.childNodes.length;if(parent&&(!parent[doneName]||!elem.nodeIndex)){var count=1;for(var node=parent.firstChild;node;node=node.nextSibling){if(node.nodeType==1){node.nodeIndex=count++;}}
parent[doneName]=count-1;}
if(type=="first"){return elem.nodeIndex==1;}else if(type=="last"){return elem.nodeIndex==parent[doneName];}else if(type=="only"){return parent[doneName]==1;}else if(type=="nth"){var add=false,first=match[2],last=match[3];if(first==1&&last==0){return true;}
if(first==0){if(elem.nodeIndex==last){add=true;}}else if((elem.nodeIndex-last)%first==0&&(elem.nodeIndex-last)/first>=0){add=true;}
return add;}},PSEUDO:function(elem,match,i,array){var name=match[1],filter=Expr.filters[name];if(filter){return filter(elem,i,match,array);}else if(name==="contains"){return(elem.textContent||elem.innerText||"").indexOf(match[3])>=0;}else if(name==="not"){var not=match[3];for(var i=0,l=not.length;i<l;i++){if(not[i]===elem){return false;}}
return true;}},ID:function(elem,match){return elem.nodeType===1&&elem.getAttribute("id")===match;},TAG:function(elem,match){return(match==="*"&&elem.nodeType===1)||elem.nodeName===match;},CLASS:function(elem,match){return match.test(elem.className);},ATTR:function(elem,match){var result=Expr.attrHandle[match[1]]?Expr.attrHandle[match[1]](elem):elem[match[1]]||elem.getAttribute(match[1]),value=result+"",type=match[2],check=match[4];return result==null?false:type==="="?value===check:type==="*="?value.indexOf(check)>=0:type==="~="?(" "+value+" ").indexOf(check)>=0:!match[4]?result:type==="!="?value!=check:type==="^="?value.indexOf(check)===0:type==="$="?value.substr(value.length-check.length)===check:type==="|="?value===check||value.substr(0,check.length+1)===check+"-":false;},POS:function(elem,match,i,array){var name=match[2],filter=Expr.setFilters[name];if(filter){return filter(elem,i,match,array);}}}};for(var type in Expr.match){Expr.match[type]=RegExp(Expr.match[type].source+/(?![^\[]*\])(?![^\(]*\))/.source);}
var makeArray=function(array,results){array=Array.prototype.slice.call(array);if(results){results.push.apply(results,array);return results;}
return array;};try{Array.prototype.slice.call(document.documentElement.childNodes);}catch(e){makeArray=function(array,results){var ret=results||[];if(toString.call(array)==="[object Array]"){Array.prototype.push.apply(ret,array);}else{if(typeof array.length==="number"){for(var i=0,l=array.length;i<l;i++){ret.push(array[i]);}}else{for(var i=0;array[i];i++){ret.push(array[i]);}}}
return ret;};}
(function(){var form=document.createElement("form"),id="script"+(new Date).getTime();form.innerHTML="<input name='"+id+"'/>";var root=document.documentElement;root.insertBefore(form,root.firstChild);if(!!document.getElementById(id)){Expr.find.ID=function(match,context){if(context.getElementById){var m=context.getElementById(match[1]);return m?m.id===match[1]||m.getAttributeNode&&m.getAttributeNode("id").nodeValue===match[1]?[m]:undefined:[];}};Expr.filter.ID=function(elem,match){var node=elem.getAttributeNode&&elem.getAttributeNode("id");return elem.nodeType===1&&node&&node.nodeValue===match;};}
root.removeChild(form);})();(function(){var div=document.createElement("div");div.appendChild(document.createComment(""));if(div.getElementsByTagName("*").length>0){Expr.find.TAG=function(match,context){var results=context.getElementsByTagName(match[1]);if(match[1]==="*"){var tmp=[];for(var i=0;results[i];i++){if(results[i].nodeType===1){tmp.push(results[i]);}}
results=tmp;}
return results;};}
div.innerHTML="<a href='#'></a>";if(div.firstChild.getAttribute("href")!=="#"){Expr.attrHandle.href=function(elem){return elem.getAttribute("href",2);};}})();if(document.querySelectorAll)(function(){var oldSizzle=Sizzle;Sizzle=function(query,context,extra,seed){context=context||document;if(!seed&&context.nodeType===9){try{return makeArray(context.querySelectorAll(query),extra);}catch(e){}}
return oldSizzle(query,context,extra,seed);};Sizzle.find=oldSizzle.find;Sizzle.filter=oldSizzle.filter;Sizzle.selectors=oldSizzle.selectors;Sizzle.matches=oldSizzle.matches;})();if(document.documentElement.getElementsByClassName){Expr.order.splice(1,0,"CLASS");Expr.find.CLASS=function(match,context){return context.getElementsByClassName(match[1]);};}
function dirNodeCheck(dir,cur,doneName,checkSet,nodeCheck,isXML){for(var i=0,l=checkSet.length;i<l;i++){var elem=checkSet[i];if(elem){elem=elem[dir];var match=false;while(elem&&elem.nodeType){var done=elem[doneName];if(done){match=checkSet[done];break;}
if(elem.nodeType===1&&!isXML)
elem[doneName]=i;if(elem.nodeName===cur){match=elem;break;}
elem=elem[dir];}
checkSet[i]=match;}}}
function dirCheck(dir,cur,doneName,checkSet,nodeCheck,isXML){for(var i=0,l=checkSet.length;i<l;i++){var elem=checkSet[i];if(elem){elem=elem[dir];var match=false;while(elem&&elem.nodeType){if(elem[doneName]){match=checkSet[elem[doneName]];break;}
if(elem.nodeType===1){if(!isXML)
elem[doneName]=i;if(typeof cur!=="string"){if(elem===cur){match=true;break;}}else if(Sizzle.filter(cur,[elem]).length>0){match=elem;break;}}
elem=elem[dir];}
checkSet[i]=match;}}}
var contains=document.compareDocumentPosition?function(a,b){return a.compareDocumentPosition(b)&16;}:function(a,b){return a!==b&&(a.contains?a.contains(b):true);};var isXML=function(elem){return elem.documentElement&&!elem.body||elem.tagName&&elem.ownerDocument&&!elem.ownerDocument.body;};jQuery.find=Sizzle;jQuery.filter=Sizzle.filter;jQuery.expr=Sizzle.selectors;jQuery.expr[":"]=jQuery.expr.filters;Sizzle.selectors.filters.hidden=function(elem){return"hidden"===elem.type||jQuery.css(elem,"display")==="none"||jQuery.css(elem,"visibility")==="hidden";};Sizzle.selectors.filters.visible=function(elem){return"hidden"!==elem.type&&jQuery.css(elem,"display")!=="none"&&jQuery.css(elem,"visibility")!=="hidden";};Sizzle.selectors.filters.animated=function(elem){return jQuery.grep(jQuery.timers,function(fn){return elem===fn.elem;}).length;};jQuery.multiFilter=function(expr,elems,not){if(not){expr=":not("+expr+")";}
return Sizzle.matches(expr,elems);};jQuery.dir=function(elem,dir){var matched=[],cur=elem[dir];while(cur&&cur!=document){if(cur.nodeType==1)
matched.push(cur);cur=cur[dir];}
return matched;};jQuery.nth=function(cur,result,dir,elem){result=result||1;var num=0;for(;cur;cur=cur[dir])
if(cur.nodeType==1&&++num==result)
break;return cur;};jQuery.sibling=function(n,elem){var r=[];for(;n;n=n.nextSibling){if(n.nodeType==1&&n!=elem)
r.push(n);}
return r;};return;window.Sizzle=Sizzle;})();jQuery.event={add:function(elem,types,handler,data){if(elem.nodeType==3||elem.nodeType==8)
return;if(elem.setInterval&&elem!=window)
elem=window;if(!handler.guid)
handler.guid=this.guid++;if(data!==undefined){var fn=handler;handler=this.proxy(fn);handler.data=data;}
var events=jQuery.data(elem,"events")||jQuery.data(elem,"events",{}),handle=jQuery.data(elem,"handle")||jQuery.data(elem,"handle",function(){return typeof jQuery!=="undefined"&&!jQuery.event.triggered?jQuery.event.handle.apply(arguments.callee.elem,arguments):undefined;});handle.elem=elem;jQuery.each(types.split(/\s+/),function(index,type){var namespaces=type.split(".");type=namespaces.shift();handler.type=namespaces.slice().sort().join(".");var handlers=events[type];if(jQuery.event.specialAll[type])
jQuery.event.specialAll[type].setup.call(elem,data,namespaces);if(!handlers){handlers=events[type]={};if(!jQuery.event.special[type]||jQuery.event.special[type].setup.call(elem,data,namespaces)===false){if(elem.addEventListener)
elem.addEventListener(type,handle,false);else if(elem.attachEvent)
elem.attachEvent("on"+type,handle);}}
handlers[handler.guid]=handler;jQuery.event.global[type]=true;});elem=null;},guid:1,global:{},remove:function(elem,types,handler){if(elem.nodeType==3||elem.nodeType==8)
return;var events=jQuery.data(elem,"events"),ret,index;if(events){if(types===undefined||(typeof types==="string"&&types.charAt(0)=="."))
for(var type in events)
this.remove(elem,type+(types||""));else{if(types.type){handler=types.handler;types=types.type;}
jQuery.each(types.split(/\s+/),function(index,type){var namespaces=type.split(".");type=namespaces.shift();var namespace=RegExp("(^|\\.)"+namespaces.slice().sort().join(".*\\.")+"(\\.|$)");if(events[type]){if(handler)
delete events[type][handler.guid];else
for(var handle in events[type])
if(namespace.test(events[type][handle].type))
delete events[type][handle];if(jQuery.event.specialAll[type])
jQuery.event.specialAll[type].teardown.call(elem,namespaces);for(ret in events[type])break;if(!ret){if(!jQuery.event.special[type]||jQuery.event.special[type].teardown.call(elem,namespaces)===false){if(elem.removeEventListener)
elem.removeEventListener(type,jQuery.data(elem,"handle"),false);else if(elem.detachEvent)
elem.detachEvent("on"+type,jQuery.data(elem,"handle"));}
ret=null;delete events[type];}}});}
for(ret in events)break;if(!ret){var handle=jQuery.data(elem,"handle");if(handle)handle.elem=null;jQuery.removeData(elem,"events");jQuery.removeData(elem,"handle");}}},trigger:function(event,data,elem,bubbling){var type=event.type||event;if(!bubbling){event=typeof event==="object"?event[expando]?event:jQuery.extend(jQuery.Event(type),event):jQuery.Event(type);if(type.indexOf("!")>=0){event.type=type=type.slice(0,-1);event.exclusive=true;}
if(!elem){event.stopPropagation();if(this.global[type])
jQuery.each(jQuery.cache,function(){if(this.events&&this.events[type])
jQuery.event.trigger(event,data,this.handle.elem);});}
if(!elem||elem.nodeType==3||elem.nodeType==8)
return undefined;event.result=undefined;event.target=elem;data=jQuery.makeArray(data);data.unshift(event);}
event.currentTarget=elem;var handle=jQuery.data(elem,"handle");if(handle)
handle.apply(elem,data);if((!elem[type]||(jQuery.nodeName(elem,'a')&&type=="click"))&&elem["on"+type]&&elem["on"+type].apply(elem,data)===false)
event.result=false;if(!bubbling&&elem[type]&&!event.isDefaultPrevented()&&!(jQuery.nodeName(elem,'a')&&type=="click")){this.triggered=true;try{elem[type]();}catch(e){}}
this.triggered=false;if(!event.isPropagationStopped()){var parent=elem.parentNode||elem.ownerDocument;if(parent)
jQuery.event.trigger(event,data,parent,true);}},handle:function(event){var all,handlers;event=arguments[0]=jQuery.event.fix(event||window.event);var namespaces=event.type.split(".");event.type=namespaces.shift();all=!namespaces.length&&!event.exclusive;var namespace=RegExp("(^|\\.)"+namespaces.slice().sort().join(".*\\.")+"(\\.|$)");handlers=(jQuery.data(this,"events")||{})[event.type];for(var j in handlers){var handler=handlers[j];if(all||namespace.test(handler.type)){event.handler=handler;event.data=handler.data;var ret=handler.apply(this,arguments);if(ret!==undefined){event.result=ret;if(ret===false){event.preventDefault();event.stopPropagation();}}
if(event.isImmediatePropagationStopped())
break;}}},props:"altKey attrChange attrName bubbles button cancelable charCode clientX clientY ctrlKey currentTarget data detail eventPhase fromElement handler keyCode metaKey newValue originalTarget pageX pageY prevValue relatedNode relatedTarget screenX screenY shiftKey srcElement target toElement view wheelDelta which".split(" "),fix:function(event){if(event[expando])
return event;var originalEvent=event;event=jQuery.Event(originalEvent);for(var i=this.props.length,prop;i;){prop=this.props[--i];event[prop]=originalEvent[prop];}
if(!event.target)
event.target=event.srcElement||document;if(event.target.nodeType==3)
event.target=event.target.parentNode;if(!event.relatedTarget&&event.fromElement)
event.relatedTarget=event.fromElement==event.target?event.toElement:event.fromElement;if(event.pageX==null&&event.clientX!=null){var doc=document.documentElement,body=document.body;event.pageX=event.clientX+(doc&&doc.scrollLeft||body&&body.scrollLeft||0)-(doc.clientLeft||0);event.pageY=event.clientY+(doc&&doc.scrollTop||body&&body.scrollTop||0)-(doc.clientTop||0);}
if(!event.which&&((event.charCode||event.charCode===0)?event.charCode:event.keyCode))
event.which=event.charCode||event.keyCode;if(!event.metaKey&&event.ctrlKey)
event.metaKey=event.ctrlKey;if(!event.which&&event.button)
event.which=(event.button&1?1:(event.button&2?3:(event.button&4?2:0)));return event;},proxy:function(fn,proxy){proxy=proxy||function(){return fn.apply(this,arguments);};proxy.guid=fn.guid=fn.guid||proxy.guid||this.guid++;return proxy;},special:{ready:{setup:bindReady,teardown:function(){}}},specialAll:{live:{setup:function(selector,namespaces){jQuery.event.add(this,namespaces[0],liveHandler);},teardown:function(namespaces){if(namespaces.length){var remove=0,name=RegExp("(^|\\.)"+namespaces[0]+"(\\.|$)");jQuery.each((jQuery.data(this,"events").live||{}),function(){if(name.test(this.type))
remove++;});if(remove<1)
jQuery.event.remove(this,namespaces[0],liveHandler);}}}}};jQuery.Event=function(src){if(!this.preventDefault)
return new jQuery.Event(src);if(src&&src.type){this.originalEvent=src;this.type=src.type;this.timeStamp=src.timeStamp;}else
this.type=src;if(!this.timeStamp)
this.timeStamp=now();this[expando]=true;};function returnFalse(){return false;}
function returnTrue(){return true;}
jQuery.Event.prototype={preventDefault:function(){this.isDefaultPrevented=returnTrue;var e=this.originalEvent;if(!e)
return;if(e.preventDefault)
e.preventDefault();e.returnValue=false;},stopPropagation:function(){this.isPropagationStopped=returnTrue;var e=this.originalEvent;if(!e)
return;if(e.stopPropagation)
e.stopPropagation();e.cancelBubble=true;},stopImmediatePropagation:function(){this.isImmediatePropagationStopped=returnTrue;this.stopPropagation();},isDefaultPrevented:returnFalse,isPropagationStopped:returnFalse,isImmediatePropagationStopped:returnFalse};var withinElement=function(event){var parent=event.relatedTarget;while(parent&&parent!=this)
try{parent=parent.parentNode;}
catch(e){parent=this;}
if(parent!=this){event.type=event.data;jQuery.event.handle.apply(this,arguments);}};jQuery.each({mouseover:'mouseenter',mouseout:'mouseleave'},function(orig,fix){jQuery.event.special[fix]={setup:function(){jQuery.event.add(this,orig,withinElement,fix);},teardown:function(){jQuery.event.remove(this,orig,withinElement);}};});jQuery.fn.extend({bind:function(type,data,fn){return type=="unload"?this.one(type,data,fn):this.each(function(){jQuery.event.add(this,type,fn||data,fn&&data);});},one:function(type,data,fn){var one=jQuery.event.proxy(fn||data,function(event){jQuery(this).unbind(event,one);return(fn||data).apply(this,arguments);});return this.each(function(){jQuery.event.add(this,type,one,fn&&data);});},unbind:function(type,fn){return this.each(function(){jQuery.event.remove(this,type,fn);});},trigger:function(type,data){return this.each(function(){jQuery.event.trigger(type,data,this);});},triggerHandler:function(type,data){if(this[0]){var event=jQuery.Event(type);event.preventDefault();event.stopPropagation();jQuery.event.trigger(event,data,this[0]);return event.result;}},toggle:function(fn){var args=arguments,i=1;while(i<args.length)
jQuery.event.proxy(fn,args[i++]);return this.click(jQuery.event.proxy(fn,function(event){this.lastToggle=(this.lastToggle||0)%i;event.preventDefault();return args[this.lastToggle++].apply(this,arguments)||false;}));},hover:function(fnOver,fnOut){return this.mouseenter(fnOver).mouseleave(fnOut);},ready:function(fn){bindReady();if(jQuery.isReady)
fn.call(document,jQuery);else
jQuery.readyList.push(fn);return this;},live:function(type,fn){var proxy=jQuery.event.proxy(fn);proxy.guid+=this.selector+type;jQuery(document).bind(liveConvert(type,this.selector),this.selector,proxy);return this;},die:function(type,fn){jQuery(document).unbind(liveConvert(type,this.selector),fn?{guid:fn.guid+this.selector+type}:null);return this;}});function liveHandler(event){var check=RegExp("(^|\\.)"+event.type+"(\\.|$)"),stop=true,elems=[];jQuery.each(jQuery.data(this,"events").live||[],function(i,fn){if(check.test(fn.type)){var elem=jQuery(event.target).closest(fn.data)[0];if(elem)
elems.push({elem:elem,fn:fn});}});jQuery.each(elems,function(){if(!event.isImmediatePropagationStopped()&&this.fn.call(this.elem,event,this.fn.data)===false)
stop=false;});return stop;}
function liveConvert(type,selector){return["live",type,selector.replace(/\./g,"`").replace(/ /g,"|")].join(".");}
jQuery.extend({isReady:false,readyList:[],ready:function(){if(!jQuery.isReady){jQuery.isReady=true;if(jQuery.readyList){jQuery.each(jQuery.readyList,function(){this.call(document,jQuery);});jQuery.readyList=null;}
jQuery(document).triggerHandler("ready");}}});var readyBound=false;function bindReady(){if(readyBound)return;readyBound=true;if(document.addEventListener){document.addEventListener("DOMContentLoaded",function(){document.removeEventListener("DOMContentLoaded",arguments.callee,false);jQuery.ready();},false);}else if(document.attachEvent){document.attachEvent("onreadystatechange",function(){if(document.readyState==="complete"){document.detachEvent("onreadystatechange",arguments.callee);jQuery.ready();}});if(document.documentElement.doScroll&&!window.frameElement)(function(){if(jQuery.isReady)return;try{document.documentElement.doScroll("left");}catch(error){setTimeout(arguments.callee,0);return;}
jQuery.ready();})();}
jQuery.event.add(window,"load",jQuery.ready);}
jQuery.each(("blur,focus,load,resize,scroll,unload,click,dblclick,"+"mousedown,mouseup,mousemove,mouseover,mouseout,mouseenter,mouseleave,"+"change,select,submit,keydown,keypress,keyup,error").split(","),function(i,name){jQuery.fn[name]=function(fn){return fn?this.bind(name,fn):this.trigger(name);};});jQuery(window).bind('unload',function(){for(var id in jQuery.cache)
if(id!=1&&jQuery.cache[id].handle)
jQuery.event.remove(jQuery.cache[id].handle.elem);});(function(){jQuery.support={};var root=document.documentElement,script=document.createElement("script"),div=document.createElement("div"),id="script"+(new Date).getTime();div.style.display="none";div.innerHTML='   <link/><table></table><a href="/a" style="color:red;float:left;opacity:.5;">a</a><select><option>text</option></select><object><param/></object>';var all=div.getElementsByTagName("*"),a=div.getElementsByTagName("a")[0];if(!all||!all.length||!a){return;}
jQuery.support={leadingWhitespace:div.firstChild.nodeType==3,tbody:!div.getElementsByTagName("tbody").length,objectAll:!!div.getElementsByTagName("object")[0].getElementsByTagName("*").length,htmlSerialize:!!div.getElementsByTagName("link").length,style:/red/.test(a.getAttribute("style")),hrefNormalized:a.getAttribute("href")==="/a",opacity:a.style.opacity==="0.5",cssFloat:!!a.style.cssFloat,scriptEval:false,noCloneEvent:true,boxModel:null};script.type="text/javascript";try{script.appendChild(document.createTextNode("window."+id+"=1;"));}catch(e){}
root.insertBefore(script,root.firstChild);if(window[id]){jQuery.support.scriptEval=true;delete window[id];}
root.removeChild(script);if(div.attachEvent&&div.fireEvent){div.attachEvent("onclick",function(){jQuery.support.noCloneEvent=false;div.detachEvent("onclick",arguments.callee);});div.cloneNode(true).fireEvent("onclick");}
jQuery(function(){var div=document.createElement("div");div.style.width="1px";div.style.paddingLeft="1px";document.body.appendChild(div);jQuery.boxModel=jQuery.support.boxModel=div.offsetWidth===2;document.body.removeChild(div);});})();var styleFloat=jQuery.support.cssFloat?"cssFloat":"styleFloat";jQuery.props={"for":"htmlFor","class":"className","float":styleFloat,cssFloat:styleFloat,styleFloat:styleFloat,readonly:"readOnly",maxlength:"maxLength",cellspacing:"cellSpacing",rowspan:"rowSpan",tabindex:"tabIndex"};jQuery.fn.extend({_load:jQuery.fn.load,load:function(url,params,callback){if(typeof url!=="string")
return this._load(url);var off=url.indexOf(" ");if(off>=0){var selector=url.slice(off,url.length);url=url.slice(0,off);}
var type="GET";if(params)
if(jQuery.isFunction(params)){callback=params;params=null;}else if(typeof params==="object"){params=jQuery.param(params);type="POST";}
var self=this;jQuery.ajax({url:url,type:type,dataType:"html",data:params,complete:function(res,status){if(status=="success"||status=="notmodified")
self.html(selector?jQuery("<div/>").append(res.responseText.replace(/<script(.|\s)*?\/script>/g,"")).find(selector):res.responseText);if(callback)
self.each(callback,[res.responseText,status,res]);}});return this;},serialize:function(){return jQuery.param(this.serializeArray());},serializeArray:function(){return this.map(function(){return this.elements?jQuery.makeArray(this.elements):this;}).filter(function(){return this.name&&!this.disabled&&(this.checked||/select|textarea/i.test(this.nodeName)||/text|hidden|password/i.test(this.type));}).map(function(i,elem){var val=jQuery(this).val();return val==null?null:jQuery.isArray(val)?jQuery.map(val,function(val,i){return{name:elem.name,value:val};}):{name:elem.name,value:val};}).get();}});jQuery.each("ajaxStart,ajaxStop,ajaxComplete,ajaxError,ajaxSuccess,ajaxSend".split(","),function(i,o){jQuery.fn[o]=function(f){return this.bind(o,f);};});var jsc=now();jQuery.extend({get:function(url,data,callback,type){if(jQuery.isFunction(data)){callback=data;data=null;}
return jQuery.ajax({type:"GET",url:url,data:data,success:callback,dataType:type});},getScript:function(url,callback){return jQuery.get(url,null,callback,"script");},getJSON:function(url,data,callback){return jQuery.get(url,data,callback,"json");},post:function(url,data,callback,type){if(jQuery.isFunction(data)){callback=data;data={};}
return jQuery.ajax({type:"POST",url:url,data:data,success:callback,dataType:type});},ajaxSetup:function(settings){jQuery.extend(jQuery.ajaxSettings,settings);},ajaxSettings:{url:location.href,global:true,type:"GET",contentType:"application/x-www-form-urlencoded",processData:true,async:true,xhr:function(){return window.ActiveXObject?new ActiveXObject("Microsoft.XMLHTTP"):new XMLHttpRequest();},accepts:{xml:"application/xml, text/xml",html:"text/html",script:"text/javascript, application/javascript",json:"application/json, text/javascript",text:"text/plain",_default:"*/*"}},lastModified:{},ajax:function(s){s=jQuery.extend(true,s,jQuery.extend(true,{},jQuery.ajaxSettings,s));var jsonp,jsre=/=\?(&|$)/g,status,data,type=s.type.toUpperCase();if(s.data&&s.processData&&typeof s.data!=="string")
s.data=jQuery.param(s.data);if(s.dataType=="jsonp"){if(type=="GET"){if(!s.url.match(jsre))
s.url+=(s.url.match(/\?/)?"&":"?")+(s.jsonp||"callback")+"=?";}else if(!s.data||!s.data.match(jsre))
s.data=(s.data?s.data+"&":"")+(s.jsonp||"callback")+"=?";s.dataType="json";}
if(s.dataType=="json"&&(s.data&&s.data.match(jsre)||s.url.match(jsre))){jsonp="jsonp"+jsc++;if(s.data)
s.data=(s.data+"").replace(jsre,"="+jsonp+"$1");s.url=s.url.replace(jsre,"="+jsonp+"$1");s.dataType="script";window[jsonp]=function(tmp){data=tmp;success();complete();window[jsonp]=undefined;try{delete window[jsonp];}catch(e){}
if(head)
head.removeChild(script);};}
if(s.dataType=="script"&&s.cache==null)
s.cache=false;if(s.cache===false&&type=="GET"){var ts=now();var ret=s.url.replace(/(\?|&)_=.*?(&|$)/,"$1_="+ts+"$2");s.url=ret+((ret==s.url)?(s.url.match(/\?/)?"&":"?")+"_="+ts:"");}
if(s.data&&type=="GET"){s.url+=(s.url.match(/\?/)?"&":"?")+s.data;s.data=null;}
if(s.global&&!jQuery.active++)
jQuery.event.trigger("ajaxStart");var parts=/^(\w+:)?\/\/([^\/?#]+)/.exec(s.url);if(s.dataType=="script"&&type=="GET"&&parts&&(parts[1]&&parts[1]!=location.protocol||parts[2]!=location.host)){var head=document.getElementsByTagName("head")[0];var script=document.createElement("script");script.src=s.url;if(s.scriptCharset)
script.charset=s.scriptCharset;if(!jsonp){var done=false;script.onload=script.onreadystatechange=function(){if(!done&&(!this.readyState||this.readyState=="loaded"||this.readyState=="complete")){done=true;success();complete();head.removeChild(script);}};}
head.appendChild(script);return undefined;}
var requestDone=false;var xhr=s.xhr();if(s.username)
xhr.open(type,s.url,s.async,s.username,s.password);else
xhr.open(type,s.url,s.async);try{if(s.data)
xhr.setRequestHeader("Content-Type",s.contentType);if(s.ifModified)
xhr.setRequestHeader("If-Modified-Since",jQuery.lastModified[s.url]||"Thu, 01 Jan 1970 00:00:00 GMT");xhr.setRequestHeader("X-Requested-With","XMLHttpRequest");xhr.setRequestHeader("Accept",s.dataType&&s.accepts[s.dataType]?s.accepts[s.dataType]+", */*":s.accepts._default);}catch(e){}
if(s.beforeSend&&s.beforeSend(xhr,s)===false){if(s.global&&!--jQuery.active)
jQuery.event.trigger("ajaxStop");xhr.abort();return false;}
if(s.global)
jQuery.event.trigger("ajaxSend",[xhr,s]);var onreadystatechange=function(isTimeout){if(xhr.readyState==0){if(ival){clearInterval(ival);ival=null;if(s.global&&!--jQuery.active)
jQuery.event.trigger("ajaxStop");}}else if(!requestDone&&xhr&&(xhr.readyState==4||isTimeout=="timeout")){requestDone=true;if(ival){clearInterval(ival);ival=null;}
status=isTimeout=="timeout"?"timeout":!jQuery.httpSuccess(xhr)?"error":s.ifModified&&jQuery.httpNotModified(xhr,s.url)?"notmodified":"success";if(status=="success"){try{data=jQuery.httpData(xhr,s.dataType,s);}catch(e){status="parsererror";}}
if(status=="success"){var modRes;try{modRes=xhr.getResponseHeader("Last-Modified");}catch(e){}
if(s.ifModified&&modRes)
jQuery.lastModified[s.url]=modRes;if(!jsonp)
success();}else
jQuery.handleError(s,xhr,status);complete();if(s.async)
xhr=null;}};if(s.async){var ival=setInterval(onreadystatechange,13);if(s.timeout>0)
setTimeout(function(){if(xhr){if(!requestDone)
onreadystatechange("timeout");if(xhr)
xhr.abort();}},s.timeout);}
try{xhr.send(s.data);}catch(e){jQuery.handleError(s,xhr,null,e);}
if(!s.async)
onreadystatechange();function success(){if(s.success)
s.success(data,status);if(s.global)
jQuery.event.trigger("ajaxSuccess",[xhr,s]);}
function complete(){if(s.complete)
s.complete(xhr,status);if(s.global)
jQuery.event.trigger("ajaxComplete",[xhr,s]);if(s.global&&!--jQuery.active)
jQuery.event.trigger("ajaxStop");}
return xhr;},handleError:function(s,xhr,status,e){if(s.error)s.error(xhr,status,e);if(s.global)
jQuery.event.trigger("ajaxError",[xhr,s,e]);},active:0,httpSuccess:function(xhr){try{return!xhr.status&&location.protocol=="file:"||(xhr.status>=200&&xhr.status<300)||xhr.status==304||xhr.status==1223;}catch(e){}
return false;},httpNotModified:function(xhr,url){try{var xhrRes=xhr.getResponseHeader("Last-Modified");return xhr.status==304||xhrRes==jQuery.lastModified[url];}catch(e){}
return false;},httpData:function(xhr,type,s){var ct=xhr.getResponseHeader("content-type"),xml=type=="xml"||!type&&ct&&ct.indexOf("xml")>=0,data=xml?xhr.responseXML:xhr.responseText;if(xml&&data.documentElement.tagName=="parsererror")
throw"parsererror";if(s&&s.dataFilter)
data=s.dataFilter(data,type);if(typeof data==="string"){if(type=="script")
jQuery.globalEval(data);if(type=="json")
data=window["eval"]("("+data+")");}
return data;},param:function(a){var s=[];function add(key,value){s[s.length]=encodeURIComponent(key)+'='+encodeURIComponent(value);};if(jQuery.isArray(a)||a.jquery)
jQuery.each(a,function(){add(this.name,this.value);});else
for(var j in a)
if(jQuery.isArray(a[j]))
jQuery.each(a[j],function(){add(j,this);});else
add(j,jQuery.isFunction(a[j])?a[j]():a[j]);return s.join("&").replace(/%20/g,"+");}});var elemdisplay={},fxAttrs=[["height","marginTop","marginBottom","paddingTop","paddingBottom"],["width","marginLeft","marginRight","paddingLeft","paddingRight"],["opacity"]];function genFx(type,num){var obj={};jQuery.each(fxAttrs.concat.apply([],fxAttrs.slice(0,num)),function(){obj[this]=type;});return obj;}
jQuery.fn.extend({show:function(speed,callback){if(speed){return this.animate(genFx("show",3),speed,callback);}else{for(var i=0,l=this.length;i<l;i++){var old=jQuery.data(this[i],"olddisplay");this[i].style.display=old||"";if(jQuery.css(this[i],"display")==="none"){var tagName=this[i].tagName,display;if(elemdisplay[tagName]){display=elemdisplay[tagName];}else{var elem=jQuery("<"+tagName+" />").appendTo("body");display=elem.css("display");if(display==="none")
display="block";elem.remove();elemdisplay[tagName]=display;}
this[i].style.display=jQuery.data(this[i],"olddisplay",display);}}
return this;}},hide:function(speed,callback){if(speed){return this.animate(genFx("hide",3),speed,callback);}else{for(var i=0,l=this.length;i<l;i++){var old=jQuery.data(this[i],"olddisplay");if(!old&&old!=="none")
jQuery.data(this[i],"olddisplay",jQuery.css(this[i],"display"));this[i].style.display="none";}
return this;}},_toggle:jQuery.fn.toggle,toggle:function(fn,fn2){var bool=typeof fn==="boolean";return jQuery.isFunction(fn)&&jQuery.isFunction(fn2)?this._toggle.apply(this,arguments):fn==null||bool?this.each(function(){var state=bool?fn:jQuery(this).is(":hidden");jQuery(this)[state?"show":"hide"]();}):this.animate(genFx("toggle",3),fn,fn2);},fadeTo:function(speed,to,callback){return this.animate({opacity:to},speed,callback);},animate:function(prop,speed,easing,callback){var optall=jQuery.speed(speed,easing,callback);return this[optall.queue===false?"each":"queue"](function(){var opt=jQuery.extend({},optall),p,hidden=this.nodeType==1&&jQuery(this).is(":hidden"),self=this;for(p in prop){if(prop[p]=="hide"&&hidden||prop[p]=="show"&&!hidden)
return opt.complete.call(this);if((p=="height"||p=="width")&&this.style){opt.display=jQuery.css(this,"display");opt.overflow=this.style.overflow;}}
if(opt.overflow!=null)
this.style.overflow="hidden";opt.curAnim=jQuery.extend({},prop);jQuery.each(prop,function(name,val){var e=new jQuery.fx(self,opt,name);if(/toggle|show|hide/.test(val))
e[val=="toggle"?hidden?"show":"hide":val](prop);else{var parts=val.toString().match(/^([+-]=)?([\d+-.]+)(.*)$/),start=e.cur(true)||0;if(parts){var end=parseFloat(parts[2]),unit=parts[3]||"px";if(unit!="px"){self.style[name]=(end||1)+unit;start=((end||1)/e.cur(true))*start;self.style[name]=start+unit;}
if(parts[1])
end=((parts[1]=="-="?-1:1)*end)+start;e.custom(start,end,unit);}else
e.custom(start,val,"");}});return true;});},stop:function(clearQueue,gotoEnd){var timers=jQuery.timers;if(clearQueue)
this.queue([]);this.each(function(){for(var i=timers.length-1;i>=0;i--)
if(timers[i].elem==this){if(gotoEnd)
timers[i](true);timers.splice(i,1);}});if(!gotoEnd)
this.dequeue();return this;}});jQuery.each({slideDown:genFx("show",1),slideUp:genFx("hide",1),slideToggle:genFx("toggle",1),fadeIn:{opacity:"show"},fadeOut:{opacity:"hide"}},function(name,props){jQuery.fn[name]=function(speed,callback){return this.animate(props,speed,callback);};});jQuery.extend({speed:function(speed,easing,fn){var opt=typeof speed==="object"?speed:{complete:fn||!fn&&easing||jQuery.isFunction(speed)&&speed,duration:speed,easing:fn&&easing||easing&&!jQuery.isFunction(easing)&&easing};opt.duration=jQuery.fx.off?0:typeof opt.duration==="number"?opt.duration:jQuery.fx.speeds[opt.duration]||jQuery.fx.speeds._default;opt.old=opt.complete;opt.complete=function(){if(opt.queue!==false)
jQuery(this).dequeue();if(jQuery.isFunction(opt.old))
opt.old.call(this);};return opt;},easing:{linear:function(p,n,firstNum,diff){return firstNum+diff*p;},swing:function(p,n,firstNum,diff){return((-Math.cos(p*Math.PI)/2)+0.5)*diff+firstNum;}},timers:[],timerId:null,fx:function(elem,options,prop){this.options=options;this.elem=elem;this.prop=prop;if(!options.orig)
options.orig={};}});jQuery.fx.prototype={update:function(){if(this.options.step)
this.options.step.call(this.elem,this.now,this);(jQuery.fx.step[this.prop]||jQuery.fx.step._default)(this);if((this.prop=="height"||this.prop=="width")&&this.elem.style)
this.elem.style.display="block";},cur:function(force){if(this.elem[this.prop]!=null&&(!this.elem.style||this.elem.style[this.prop]==null))
return this.elem[this.prop];var r=parseFloat(jQuery.css(this.elem,this.prop,force));return r&&r>-10000?r:parseFloat(jQuery.curCSS(this.elem,this.prop))||0;},custom:function(from,to,unit){this.startTime=now();this.start=from;this.end=to;this.unit=unit||this.unit||"px";this.now=this.start;this.pos=this.state=0;var self=this;function t(gotoEnd){return self.step(gotoEnd);}
t.elem=this.elem;jQuery.timers.push(t);if(t()&&jQuery.timerId==null){jQuery.timerId=setInterval(function(){var timers=jQuery.timers;for(var i=0;i<timers.length;i++)
if(!timers[i]())
timers.splice(i--,1);if(!timers.length){clearInterval(jQuery.timerId);jQuery.timerId=null;}},13);}},show:function(){this.options.orig[this.prop]=jQuery.attr(this.elem.style,this.prop);this.options.show=true;this.custom(this.prop=="width"||this.prop=="height"?1:0,this.cur());jQuery(this.elem).show();},hide:function(){this.options.orig[this.prop]=jQuery.attr(this.elem.style,this.prop);this.options.hide=true;this.custom(this.cur(),0);},step:function(gotoEnd){var t=now();if(gotoEnd||t>=this.options.duration+this.startTime){this.now=this.end;this.pos=this.state=1;this.update();this.options.curAnim[this.prop]=true;var done=true;for(var i in this.options.curAnim)
if(this.options.curAnim[i]!==true)
done=false;if(done){if(this.options.display!=null){this.elem.style.overflow=this.options.overflow;this.elem.style.display=this.options.display;if(jQuery.css(this.elem,"display")=="none")
this.elem.style.display="block";}
if(this.options.hide)
jQuery(this.elem).hide();if(this.options.hide||this.options.show)
for(var p in this.options.curAnim)
jQuery.attr(this.elem.style,p,this.options.orig[p]);}
if(done)
this.options.complete.call(this.elem);return false;}else{var n=t-this.startTime;this.state=n/this.options.duration;this.pos=jQuery.easing[this.options.easing||(jQuery.easing.swing?"swing":"linear")](this.state,n,0,1,this.options.duration);this.now=this.start+((this.end-this.start)*this.pos);this.update();}
return true;}};jQuery.extend(jQuery.fx,{speeds:{slow:600,fast:200,_default:400},step:{opacity:function(fx){jQuery.attr(fx.elem.style,"opacity",fx.now);},_default:function(fx){if(fx.elem.style&&fx.elem.style[fx.prop]!=null)
fx.elem.style[fx.prop]=fx.now+fx.unit;else
fx.elem[fx.prop]=fx.now;}}});if(document.documentElement["getBoundingClientRect"])
jQuery.fn.offset=function(){if(!this[0])return{top:0,left:0};if(this[0]===this[0].ownerDocument.body)return jQuery.offset.bodyOffset(this[0]);var box=this[0].getBoundingClientRect(),doc=this[0].ownerDocument,body=doc.body,docElem=doc.documentElement,clientTop=docElem.clientTop||body.clientTop||0,clientLeft=docElem.clientLeft||body.clientLeft||0,top=box.top+(self.pageYOffset||jQuery.boxModel&&docElem.scrollTop||body.scrollTop)-clientTop,left=box.left+(self.pageXOffset||jQuery.boxModel&&docElem.scrollLeft||body.scrollLeft)-clientLeft;return{top:top,left:left};};else
jQuery.fn.offset=function(){if(!this[0])return{top:0,left:0};if(this[0]===this[0].ownerDocument.body)return jQuery.offset.bodyOffset(this[0]);jQuery.offset.initialized||jQuery.offset.initialize();var elem=this[0],offsetParent=elem.offsetParent,prevOffsetParent=elem,doc=elem.ownerDocument,computedStyle,docElem=doc.documentElement,body=doc.body,defaultView=doc.defaultView,prevComputedStyle=defaultView.getComputedStyle(elem,null),top=elem.offsetTop,left=elem.offsetLeft;while((elem=elem.parentNode)&&elem!==body&&elem!==docElem){computedStyle=defaultView.getComputedStyle(elem,null);top-=elem.scrollTop,left-=elem.scrollLeft;if(elem===offsetParent){top+=elem.offsetTop,left+=elem.offsetLeft;if(jQuery.offset.doesNotAddBorder&&!(jQuery.offset.doesAddBorderForTableAndCells&&/^t(able|d|h)$/i.test(elem.tagName)))
top+=parseInt(computedStyle.borderTopWidth,10)||0,left+=parseInt(computedStyle.borderLeftWidth,10)||0;prevOffsetParent=offsetParent,offsetParent=elem.offsetParent;}
if(jQuery.offset.subtractsBorderForOverflowNotVisible&&computedStyle.overflow!=="visible")
top+=parseInt(computedStyle.borderTopWidth,10)||0,left+=parseInt(computedStyle.borderLeftWidth,10)||0;prevComputedStyle=computedStyle;}
if(prevComputedStyle.position==="relative"||prevComputedStyle.position==="static")
top+=body.offsetTop,left+=body.offsetLeft;if(prevComputedStyle.position==="fixed")
top+=Math.max(docElem.scrollTop,body.scrollTop),left+=Math.max(docElem.scrollLeft,body.scrollLeft);return{top:top,left:left};};jQuery.offset={initialize:function(){if(this.initialized)return;var body=document.body,container=document.createElement('div'),innerDiv,checkDiv,table,td,rules,prop,bodyMarginTop=body.style.marginTop,html='<div style="position:absolute;top:0;left:0;margin:0;border:5px solid #000;padding:0;width:1px;height:1px;"><div></div></div><table style="position:absolute;top:0;left:0;margin:0;border:5px solid #000;padding:0;width:1px;height:1px;"cellpadding="0"cellspacing="0"><tr><td></td></tr></table>';rules={position:'absolute',top:0,left:0,margin:0,border:0,width:'1px',height:'1px',visibility:'hidden'};for(prop in rules)container.style[prop]=rules[prop];container.innerHTML=html;body.insertBefore(container,body.firstChild);innerDiv=container.firstChild,checkDiv=innerDiv.firstChild,td=innerDiv.nextSibling.firstChild.firstChild;this.doesNotAddBorder=(checkDiv.offsetTop!==5);this.doesAddBorderForTableAndCells=(td.offsetTop===5);innerDiv.style.overflow='hidden',innerDiv.style.position='relative';this.subtractsBorderForOverflowNotVisible=(checkDiv.offsetTop===-5);body.style.marginTop='1px';this.doesNotIncludeMarginInBodyOffset=(body.offsetTop===0);body.style.marginTop=bodyMarginTop;body.removeChild(container);this.initialized=true;},bodyOffset:function(body){jQuery.offset.initialized||jQuery.offset.initialize();var top=body.offsetTop,left=body.offsetLeft;if(jQuery.offset.doesNotIncludeMarginInBodyOffset)
top+=parseInt(jQuery.curCSS(body,'marginTop',true),10)||0,left+=parseInt(jQuery.curCSS(body,'marginLeft',true),10)||0;return{top:top,left:left};}};jQuery.fn.extend({position:function(){var left=0,top=0,results;if(this[0]){var offsetParent=this.offsetParent(),offset=this.offset(),parentOffset=/^body|html$/i.test(offsetParent[0].tagName)?{top:0,left:0}:offsetParent.offset();offset.top-=num(this,'marginTop');offset.left-=num(this,'marginLeft');parentOffset.top+=num(offsetParent,'borderTopWidth');parentOffset.left+=num(offsetParent,'borderLeftWidth');results={top:offset.top-parentOffset.top,left:offset.left-parentOffset.left};}
return results;},offsetParent:function(){var offsetParent=this[0].offsetParent||document.body;while(offsetParent&&(!/^body|html$/i.test(offsetParent.tagName)&&jQuery.css(offsetParent,'position')=='static'))
offsetParent=offsetParent.offsetParent;return jQuery(offsetParent);}});jQuery.each(['Left','Top'],function(i,name){var method='scroll'+name;jQuery.fn[method]=function(val){if(!this[0])return null;return val!==undefined?this.each(function(){this==window||this==document?window.scrollTo(!i?val:jQuery(window).scrollLeft(),i?val:jQuery(window).scrollTop()):this[method]=val;}):this[0]==window||this[0]==document?self[i?'pageYOffset':'pageXOffset']||jQuery.boxModel&&document.documentElement[method]||document.body[method]:this[0][method];};});jQuery.each(["Height","Width"],function(i,name){var tl=i?"Left":"Top",br=i?"Right":"Bottom";jQuery.fn["inner"+name]=function(){return this[name.toLowerCase()]()+
num(this,"padding"+tl)+
num(this,"padding"+br);};jQuery.fn["outer"+name]=function(margin){return this["inner"+name]()+
num(this,"border"+tl+"Width")+
num(this,"border"+br+"Width")+
(margin?num(this,"margin"+tl)+num(this,"margin"+br):0);};var type=name.toLowerCase();jQuery.fn[type]=function(size){return this[0]==window?document.compatMode=="CSS1Compat"&&document.documentElement["client"+name]||document.body["client"+name]:this[0]==document?Math.max(document.documentElement["client"+name],document.body["scroll"+name],document.documentElement["scroll"+name],document.body["offset"+name],document.documentElement["offset"+name]):size===undefined?(this.length?jQuery.css(this[0],type):null):this.css(type,typeof size==="string"?size:size+"px");};});})();