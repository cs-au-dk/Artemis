Object.beget = function(o) {
    var F = function() {};
    F.prototype = o;

    return new F();
};

Function.prototype.method = function(name, func) {
    if (!this.prototype[name]) {
        this.prototype[name] = func;
    }
};

Array.prototype.append = function(el) {
    this[this.length] = el;
    return this;
};

var exists = function(value) {
    return !(value === null || value === undefined);
};

var vector_to_rgba = function(v) {
    if (v) {
        var inner = v.elements.map(function(component) {
            return Math.floor(component);
        }).join(', ');

        return 'rgba(' + inner + ')';
    } else {
        return '';
    }
};

// basic framework namespace
var flux = {
    browser: {
        dim: function() {
            var w = arguments[0];
            var h = arguments[1];

            // if two arguments are provided, they represent width and height
            if (w && h) {
                this.w = w;
                this.h = h;
                this.dimension = $V([w, h]);
            // if only one, it is a vector
            } else if (w) {
                this.w = w.elements[0];
                this.h = w.elements[1];
                this.dimension = w;
            }

            // if none (or any), simply return dimension
            return this.dimension;
        }
    }
};

flux.bounds = function(xlow, xhigh, ylow, yhigh) {
    var that = [];
    var checks = [Math.min, Math.max];

    that.x = [xlow, xhigh];
    that.y = [ylow, yhigh];
    that[0] = that.x;
    that[1] = that.y;

    that.extreme = function(way) {
        return [that[0][way], that[1][way]];
    };

    that.copy = function() {
        return flux.bounds(that.x[0], that.x[1], that.y[0], that.y[1]);
    };

    that.range = function(axis) {
        return that[axis][1] - that[axis][0];
    };

    that.low = function() {
        return that.extreme(0);
    };

    that.high = function() {
        return that.extreme(1);
    };

    that.width = function() {
        return that.range(0);
    };

    that.height = function() {
        return that.range(1);
    };

    that.randomValue = function(axis) {
        return Math.random()*that.range(axis)+that[axis][0];
    };

    that.randomPoint = function() {
        return [0, 1].map(that.randomValue);
    };

    // unions with another bounds object
    that.union = function(other) {
        for (var a = 0; a < 2; a++) {
            for (var b = 0; b < 2; b++) {
                that[a][b] = checks[b](that[a][b], other[a][b]);
            }
        }

        return that;
    };

    // grows to ensure it encloses the given point
    that.include = function(point) {
        for (var a = 0; a < 2; a++) {
            for (var b = 0; b < 2; b++) {
                that[a][b] = checks[b](that[a][b], point.o(a));
            }
        }

        return that;
    };

    // shifts the entire object by the given vector
    that.translate = function(point) {
        for (var a = 0; a < 2; a++) {
            for (var b = 0; b < 2; b++) {
                that[a][b] += point.o(a);
            }
        }

        return that;
    };

    // check whether the given point is within these bounds
    // returning a list of comparision values by axis
    that.check = function(point) {
        return point.elements.map(function(a, index) {
            return (a < that[index][0]) ? - 1 : (a > that[index][1]) ? 1 : 0;
        });
    };

    // check whether the given point is within these bounds
    // returning a boolean
    that.inside = function(point) {
        return that.check(point).inject(true, function(side, a, index) {
            return side && a === 0;
        });
    };

    that.shapeFor = function() {
        return flux.shape({ops: [
            {op: 'move', to: $V([that.x[0], that.y[0]])},
            {op: 'line', to: $V([that.x[1], that.y[0]])},
            {op: 'line', to: $V([that.x[1], that.y[1]])},
            {op: 'line', to: $V([that.x[0], that.y[1]])}
        ]});
    };

    that.scale = function(factor) {
        var w = that.width();
        var h = that.height();
        var wfactor = (w*factor-w)*0.5;
        var hfactor = (h*factor-h)*0.5;

        return flux.bounds(that.x[0]-wfactor, that.x[1]+wfactor, that.y[0]-hfactor, that.y[1]+hfactor);
    };

    return that;
};

flux.compositebounds = function() {

};

// provide objects to represent atomic drawing operations
flux.op = function() {
    var result = {};

    result.base = function(spec) {
        var that = {};

        that.op = spec.op;
        that.method = spec.method || 'lineTo';
        that.to = spec.to ? $V([spec.to.elements[0], spec.to.elements[1]]) : $V([0, 0]);

        that.args = function() {
            return that.to.elements;
        };

        that.prod = function(box) {
            box.include(that.to);
        };

        that.dup = function() {
            return result.base(that);
        };

        that.between = function(other, cycles) {
            return [flux.tweenV({
                obj: that,
                property: 'to',
                to: other.to,
                cycles: cycles
            })];
        };

        return that;
    };

    result.line = function(spec) {
        spec.method = 'lineTo';

        var that = result.base(spec);

        that.dup = function() {
            return result.line(that);
        };

        return that;
    };

    result.move = function(spec) {
        spec.method = 'moveTo';

        var that = result.base(spec);

        that.dup = function() {
            return result.move(that);
        };

        return that;
    };

    result.text = function(spec) {
        spec.method = 'opText';
        var that = result.base(spec);

        that.size = spec.size || 12;
        that.string = spec.string || '';

        that.dup = function() {
            return result.text(that);
        };

        that.args = function() {
            return [true, that.size, that.to.o(0), that.to.o(1), that.string];
        };

        that.prod = function(box) {
            var renderLength = function(string) {
                return CanvasTextFunctions.measure(true, that.size, string);
            };

            // find the longest line to use as the outermost horizontal boundary
            var lines = that.string.split('\n');
            var longest = {length: renderLength(lines[0]), line: lines[0]};
            for (var index=1; index < lines.length; index++) {
                var possible = renderLength(line[index]);
                if (possible > longest.length) {
                    longest = {length: possible, line: line[index]};
                }
            }

            box.union(flux.bounds(
                that.to.o(0),
                that.to.o(0) + longest.length,
                that.to.o(1) - that.size,
                that.to.o(1) + that.size*lines.length
            ));
        };

        return that;
    };

    result.arc = function(spec) {
        spec.method = 'arc';

        var that = result.base(spec);

        that.radius = spec.radius || 10;
        that.arc = spec.arc || $V([0, Math.PI*2]);
        that.clockwise = spec.clockwise || true;

        that.args = function() {
            return that.to.elements.concat([that.radius].concat(that.arc.elements).append(that.clockwise));
        };

        that.between = function(other, cycles) {
            return [
                flux.tweenV({obj: that,
                    property: 'to',
                    to: other.to,
                    cycles: cycles}),
                flux.tweenN({obj: that,
                    property: 'radius',
                    to: other.radius,
                    cycles: cycles}),
                flux.tweenN({obj: that,
                    property: 'arc',
                    to: other.arc,
                    cycles: cycles})
            ];
        };

        that.prod = function(box) {
            box.union(flux.bounds(
                that.to.o(0) - that.radius,
                that.to.o(0) + that.radius,
                that.to.o(1) - that.radius,
                that.to.o(1) + that.radius
            ));
        };

        that.dup = function() {
            return result.arc(that);
        };

        return that;
    };

    result.bezier = function(spec) {
        spec.method = 'bezierCurveTo';
        spec.to = spec.to ? spec.to.dup() : $V([10, 10]);

        var that = result.base(spec);

        that.control1 = spec.control1 ? spec.control1.dup() : $V([0, 0]);
        that.control2 = spec.control2 ? spec.control2.dup() : $V([0, 0]);

        that.args = function() {
            return that.control1.elements.concat(that.control2.elements).concat(that.to.elements);
        };

        that.prod = function(box) {
            box.include(that.to);
            box.include(that.control1);
            box.include(that.control2);
        };

        that.between = function(other, cycles) {
            return [
                flux.tweenV({
                    obj: that,
                    property: 'to',
                    to: other.to,
                    cycles: cycles}),
                flux.tweenV({
                    obj: that,
                    property: 'control1',
                    to: other.control1,
                    cycles: cycles}),
                flux.tweenV({
                    obj: that,
                    property: 'control2',
                    to: other.control2,
                    cycles: cycles})
            ];
        };

        that.dup = function() {
            return result.bezier(that);
        };

        return that;
    };

    return result;
}();

flux.shape = function(spec) {
    var that = {};

    that.ops = spec.ops ? spec.ops.map(function(op) {return flux.op[op.op](op);}) : null || [];
    that.color = spec.color;
    that.fill = spec.fill || 'fill';

    that.between = function(other, cycles, postcycle) {
        return that.ops.inject([], function(tweens, op, index) {
            return tweens.concat(op.between(other.ops[index], cycles));
        });
    };

    that.dup = function() {
        return flux.shape({ops: that.ops.map(function(vertex) {return vertex.dup();})});
    };

    // construct a simple bounding box to tell if further bounds checking is necessary
    that.boxFor = function() {
        var box = flux.bounds(0, 0, 0, 0);

        that.ops.each(function(vertex) {
            vertex.prod(box);
        });

        return box;
    };

    that.box = that.boxFor();

    that.draw = function(context) {
        context.beginPath();

        if (that.color) context[that.fill+'Style'] = vector_to_rgba(that.color);

        that.ops.each(function(vertex) {
            context[vertex.method].apply(context, vertex.args());
        });

        context.closePath();
        context[that.fill]();
    };

    return that;
};

// generic base tween object
flux.tween = function(spec) {
    var that = {};

    that.obj = spec.obj || spec;
    that.property = spec.property || ((spec.property === 0) ? spec.property : 'this');
    that.target = spec.target || function(value) {return value === 0;};
    that.step = spec.step || function(value) {return value - 1;};

    that.value = function() {
        return that.obj[that.property];
    };

    that.cycle = function() {
        if (that.target(that.value())) {
            return false;
        } else {
            that.obj[that.property] = that.step(that.value());
            return true;
        }
    };

    return that;
};

// tween object for numbers
flux.tweenN = function(spec) {
    var that = flux.tween(spec);
    var increment = spec.increment || (spec.cycles ? ((spec.to - spec.obj[spec.property]) / spec.cycles) : 1);

    var greater = function(where, to) {return where >= to;};
    var less = function(where, to) {return where <= to;};

    that.to = spec.to || 0;
    that.test = spec.test || ((that.value() < that.to) ? greater : less);

    that.target = spec.target || function(value) {
        return that.test(value, that.to);
    };

    that.step = spec.step || function(value) {
        return value + increment;
    };

    return that;
};

// tween object for vectors
flux.tweenV = function(spec) {
    var that = {};

    that.obj = spec.obj || spec;
    that.property = spec.property || 'this';
    that.to = spec.to || $V([1, 1]);
    that.cycles = spec.cycles || 10;
    that.postcycle = spec.postcycle || function() {};
    that.posttween = spec.posttween || function() {};

    that.vector = function() {
        return that.obj[that.property];
    };

    var differing = $R(0, that.vector().dimensions() - 1).select(function(index) {
        return !(that.vector().o(index) === that.to.o(index));
    });

    that.tweens = differing.map(function(index) {
        return flux.tweenN({
            obj: that.vector().elements,
            property: index,
            to: that.to.o(index),
            cycles: that.cycles
        });
    });

    that.cycle = function() {
        that.tweens = that.tweens.select(function(tween) {return tween.cycle();});
        that.postcycle();

        if (that.tweens.length === 0) {
            that.posttween();
        }

        return that.tweens.length > 0;
    };

    return that;
};

flux.tweenEvent = function(spec) {
    spec.obj = {count: 0};
    spec.property = 'count';

    var that = flux.tween(spec);

    that.cycles = spec.cycles || 10;
    that.event = spec.event || function() {};

    that.target = function(n) {
        var met = true;

        if (n < that.cycles) {
            met = false;
        } else {
            that.event();
        }

        return met;
    };

    that.step = function(n) {
        return n += 1;
    };

    return that;
};

// representation of individual agents
flux.mote = function(spec) {
    var that = {};
    spec = spec || {};

    that.type = spec.type || 'mote';
    that.supermote = spec.supermote || null;
    that.submotes = spec.submotes || [];

    that.pos = spec.pos || $V([0, 0]);
    that.shape = spec.shape || flux.shape({ops: [{op: 'arc', to: $V([500, 500]), radius: 50, arc: $V([0, Math.PI*2])}]});
    that.orientation = (spec.orientation === undefined) ? Math.random()*2*Math.PI : spec.orientation;
    that.rotation = (spec.rotation === undefined) ? 0 : spec.rotation;
    that.velocity = spec.velocity || $V([0, 0]);

    that.shapes = spec.shapes || [that.shape];
    that.visible = spec.visible === undefined ? true : spec.visible;

    that.color = spec.color || $V([200, 200, 200, 1]);
    that.scale = spec.scale || $V([1, 1]);
    that.fill = spec.fill || 'fill';
    that.lineWidth = spec.lineWidth || 1;
    that.outline = spec.outline || null;
    that.bounds = spec.bounds;
    that.transform = spec.transform || 'pos';
    that.paused = false;

    that.tweens = [];

    that.future = [];
    that.neighbors = [];

    that.mouseDown = function(mouse) {};
    that.mouseUp = function(mouse) {};
    that.mouseClick = function(mouse) {};
    that.mouseIn = function(mouse) {};
    that.mouseOut = function(mouse) {};
    that.mouseMove = function(mouse) {};

    // absolute is a function to find the absolute position of the mote
    // with the position, orientation and scale each supermote in this mote's
    // heirarchy of supermotes taken into consideration.

    // rise takes a position and recursively applies the transformations of
    // all supermotes onto it
    that.rise = function(pos) {
        pos = that.transform === 'screen' ? pos.add(that.pos.times(flux.browser.dim())) : pos;
        return that.supermote ? that.supermote.rise(that.supermote.extrovert(pos)) : pos;
    };

    // find_absolute is for the cache, so that the absolute position does not
    // need to be calculated every time it is accessed, only when the
    // position or orientation of it or one of its supermotes is changed.
    var find_absolute = function() {
        return that.rise(that.pos);
    };
    that.absolute = cache(find_absolute);
    that.absolute.expiring = function() {
        that.submotes.each(function(submote) {
            submote.absolute.expire();
        });
    };

    that.contains = function(point) {
        return that.box.inside(point.subtract(that.absolute()));
    };

    // construct a simple bounding box to tell if further bounds checking is necessary
    that.findBox = function() {
        var box = flux.bounds(0, 0, 0, 0);

        box = that.shapes.inject(box, function(grow, shape) {
            return grow.union(shape.box);
        });

        that.submotes.each(function(submote) {
            box.union(submote.box);
        });

        that.box = box;
        return box;
    };

    that.findBox();

    that.findIn = function(mouse, pos) {
        if (that.contains(pos) && !mouse.inside.include(that)) {
            mouse.inside.append(that);
            that.mouseIn(mouse);
        }

        that.submotes.invoke('findIn', mouse, pos);
    };

    var findColorSpec = function(prop) {
        return function() {return vector_to_rgba(that[prop]);};
    };

    that.color_spec = cache(findColorSpec('color'));
    that.outline_spec = cache(findColorSpec('outline'));

    that.tweenColor = function(color, cycles, posttween) {
        posttween = posttween || function() {};

        that.tweens.append(flux.tweenV({
            obj: that,
            property: 'color',
            to: color,
            cycles: cycles,
            postcycle: function() {that.color_spec.expire();},
            posttween: posttween
        }));

        return that;
    };

    that.tweenPos = function(to, cycles, posttween) {
        that.tweens.append(flux.tweenV({
            obj: that,
            property: 'pos',
            to: to,
            cycles: cycles,
            postcycle: function() {that.absolute.expire();},
            posttween: posttween
        }));

        return that;
    };

    that.tweenOrientation = function(orientation, cycles, posttween) {
        that.tweens.append(flux.tweenN({
            obj: that,
            property: 'orientation',
            to: orientation,
            cycles: cycles,
            posttween: posttween
        }));

        return that;
    };

    that.tweenScale = function(scale, cycles) {
        that.tweens.append(flux.tweenV({
            obj: that,
            property: 'scale',
            to: scale,
            cycles: cycles
        }));

        return that;
    };

    that.tweenShape = function(shape, cycles) {
        var tween = that.shape.between(shape, cycles);
        that.tweens = that.tweens.concat(tween);

        return that;
    };

    that.tweenEvent = function(event, cycles) {
        var tween = flux.tweenEvent({event: event, cycles: cycles});
        that.tweens = that.tweens.concat(tween);

        return that;
    };

    that.expireSupermotes = function() {
        that.supermotes.expire();
        that.absolute.expire();
        that.submotes.each(function(submote) {
            submote.expireSupermotes();
        });
    };

    that.attach = function(other) {
        other.orientation -= that.orientation;
        if (other.supermote) {
            other.supermote.submotes = other.supermote.submotes.without(other);
        }
        that.submotes.append(other);

        other.supermote = that;
        other.expireSupermotes();
    };

    that.detach = function(other) {
        that.submotes = that.submotes.without(other);

        other.orientation += that.orientation;
//        other.pos = other.supermote.extrovert(other.pos);
        other.supermote = null;

        if (that.supermote) {
//            other.pos = that.supermote.extrovert(other.pos);
            that.supermote.attach(other);
        }

        other.absolute.expire();
    };

    that.addSubmotes = function(submotes) {
        submotes.each(function(submote) {
            that.attach(submote);
        });
    };

    that.introvert = function(pos) {
        return pos.times(that.scale.map(function(el) {return 1.0 / el;})).rotate(-that.orientation, that.pos).subtract(that.pos);
    };

    that.extrovert = function(pos) {
//        var transform = that.transform === 'screen' ? pos.add(that.pos.times(flux.browser.dim())) : pos.add(that.pos);
        var transform = pos.add(that.pos);
        return transform.rotate(that.orientation, that.pos).times(that.scale);
    };

    that.find_supermotes = function() {
        return (that.supermote === null) ? [] : that.supermote.supermotes().slice().append(that.supermote);
    };

    that.supermotes = cache(that.find_supermotes);

    that.commonSupermote = function(other) {
        if (that.supermote === null || other.supermote === null) {
            return null;
        }

        var n = that.supermotes().length - 1;
        var common = null;
        var down = -1;
        var possible = null;

        while (!common && n >= 0) {
            possible = that.supermotes()[n];
            down = other.supermotes().indexOf(possible);

            if (down >= 0) {
                common = possible;
            } else {
                n -= 1;
            }
        }

        return {
            common: common,
            up: that.supermotes().length - 1 - n,
            down: down === -1 ? other.supermotes().length : other.supermotes().length - 1 - down
        };
    };

    that.relativePos = function(other) {
        if (that.supermote === other.supermote) {
            return other.pos;
        }

        var common = that.commonSupermote(other);
        var transformed = other.pos;

        for (var extro = 0; extro < common.down; extro++) {
            transformed = other.supermotes()[(other.supermotes().length - 1) - extro].extrovert(transformed);
        }

        for (var intro = 0; intro < common.up; intro++) {
            transformed = that.supermotes()[(that.supermotes().length - common.up) + intro].introvert(transformed);
        }

        return transformed;
    };

    that.distance = function(other) {
        return that.absolute().distanceFrom(other.absolute());
    };

    that.to = function(other) {
        return other.absolute().subtract(that.absolute());
    };

    that.angleFrom = function(other) {
        return that.pos.angleFrom(other.pos);
    };

    // this finds the closest mote from a list of possible motes.
    // a predicate can be provided to filter out choices.
    that.findClosest = function(others, predicate) {
        var closestMote = null;
        var closestDistance = null;

        predicate = predicate || function(other) {return true;};

        others.each(function(other) {
            if (predicate(other)) {
                if (closestMote === null) {
                    closestMote = other;
                    closestDistance = that.distance(other);
                } else {
                    var newDistance = that.distance(other);
                    if (newDistance < closestDistance) {
                        closestMote = other;
                        closestDistance = newDistance;
                    }
                }
            }
        });

        return closestMote;
    };

    that.pause = function() {
        that.paused = true;
    };

    that.unpause = function() {
        that.paused = false;
    };

    that.perceive = spec.perceive || function(env) {
        that.submotes.each(function(submote) {
            submote.perceive(env);
        });
    };

    that.adjust = spec.adjust || function() {
        if (!that.paused) {
            that.orientation += that.rotation;

            while (that.orientation > Math.PI) {
                that.orientation -= Math.PI*2;
            } while (that.orientation < -Math.PI) {
                that.orientation += Math.PI*2;
            }

            for (var dim=0; dim < that.pos.dimensions(); dim++) {
                that.pos.elements[dim] += that.velocity.o(dim);
            }

            that.future.each(function(moment) {
                                 moment(that);
                             });
            that.future = [];

        }

        that.tweens = that.tweens.select(function(tween) {
            return tween.cycle();
        });

        that.submotes.invoke('adjust');
        that.absolute.expire();

// ----------- lazy bounds checking ---------------
        if (that.bounds) {
            var check = that.bounds.check(that.pos);

            check.each(function(result, index) {
                if (!(result === 0)) {
                    that.velocity.elements[index] = -that.velocity.elements[index];
                }
            });
        }
// -------------------------------------------------

    };

    that.drawShape = function(context, fill) {
        context.beginPath();

        that.shape.ops.each(function(vertex) {
            context[vertex.method].apply(context, vertex.args());
        });

        context.closePath();
        context[fill]();
    };

    that.draw = function(context) {
        // drawing lines to neighbors
        if (that.visible && that.neighbors.length > 1) {
            context.save();

            that.neighbors.each(function(neighbor) {
                context.lineWidth = 3;
                context.strokeStyle = that.color_spec();
                context.beginPath();
                context.moveTo.apply(context, that.pos.elements);
                context.lineTo.apply(context, that.relativePos(neighbor).elements);
                context.closePath();
                context.stroke();
            });

            context.restore();
        }

        // drawing the shape
        context.save();

        context[that.fill + 'Style'] = that.color_spec();
        context.lineWidth = that.lineWidth;

        if (that.transform === 'screen') {
            context.translate(Math.floor(that.pos.o(0)*flux.browser.w), Math.floor(that.pos.o(1)*flux.browser.h));
        } else {
            context.translate.apply(context, that.pos.elements);
        }

        context.rotate(that.orientation);
        context.scale.apply(context, that.scale.elements);

        if (that.visible) {
            var len = that.shapes.length;
            for (var index=0; index < len; index++){
                that.shapes[index].draw(context);
            }

            if (that.outline) {
                context.save();
                context.strokeStyle = that.outline_spec();
                that.drawShape(context, 'stroke');
                context.restore();
            }
        }

        that.submotes.invoke('draw', context);

        context.restore();
    };

    return that;
};

// managing the canvas for all motes
flux.canvas = function(spec) {
    var that = {};

    var canvas, context;
    var now, before, interval;

    that.motes = spec.motes || [];
    that.id = spec.id || '';

    that.transforms = that.motes.groupBy(function(mote) {
        return mote.transform;
    });

    that.down = spec.down || function(m){return null;};
    that.up = spec.up || function(m){return null;};
    that.move = spec.move || function(m){return null;};

    that.translation = spec.translation || $V([0, 0]);
    that.orientation = spec.orientation || 0;
    that.scale = spec.scale || $V([1, 1]);

    that.tweens = [];

    that.predraw = spec.predraw || function(context) {};
    that.postdraw = spec.postdraw || function(context) {};

    that.resize = spec.resize || function(browser) {};
    that.wheel = spec.wheel || function(delta) {};
    that.preventKeys = spec.preventKeys || false;

    var time = function() {
        return new Date().getTime();
    };

    that.triangulate = function() {

    };

    var keys = {};

    keys.pressed = {};
    keys.predown = function(key) {
        keys.pressed[key] = true;
        keys.down(that, key);
    };
    keys.preup = function(key) {
        delete this.pressed[key];
        keys.up(that, key);
    };

    keys.down = spec.keyDown || function(th, key) {};
    keys.up = spec.keyUp || function(th, key) {};

    var mouse = {
        pos: $V([0, 0]),
        prevpos: $V([0, 0]),

        screen: $V([0, 0]),
        prevscreen: $V([0, 0]),

        down: false,
        inside: [],

        diffpos: function() {
            return this.pos.subtract(this.prevpos);
        },

        diffscreen: function() {
            return this.screen.subtract(this.prevscreen);
        },

        posify: function(where) {
            return where.subtract(that.translation).times(that.scale.map(function(el) {return 1.0 / el;}));
        },

        deposify: function(where) {
            return where.times(that.scale).add(that.translation);
        }
    };

    that.addMote = function(mote) {
        if (!that.transforms[mote.transform]) that.transforms[mote.transform] = [];

        that.transforms[mote.transform].append(mote);
        that.motes.append(mote);
    };

    that.removeMote = function(mote) {
        that.transforms[mote.transform] = that.transforms[mote.transform].without(mote);
        that.motes = that.motes.without(mote);
    };

    that.tweenScale = function(scale, cycles) {
        var tween = flux.tweenV({
            obj: that,
            property: 'scale',
            to: scale,
            cycles: cycles
        });

        that.tweens.append(tween);
        return that;
    };

    that.tweenTranslation = function(translation, cycles) {
        var tween = flux.tweenV({
            obj: that,
            property: 'translation',
            to: translation,
            cycles: cycles
        });

        that.tweens.append(tween);
        return that;
    };

    that.tweenViewport = function(spec, cycles) {
        if (spec.scale) that.tweenScale(spec.scale, cycles);
        if (spec.translation) that.tweenTranslation(spec.translation, cycles);
    };

    var update = function() {
        before = now;
        now = time();
        interval = now - before;

        that.motes.invoke('perceive', that);
        that.motes.invoke('adjust');

        that.tweens = that.tweens.select(function(tween) {
            return tween.cycle();
        });

        draw();
    };

    var draw = function() {
        context.clearRect(0, 0, flux.browser.w, flux.browser.h);
        that.predraw(context);

        if (that.transforms['pos']) {
            context.save();
            context.translate(that.translation.o(0), that.translation.o(1));
            context.scale(that.scale.o(0), that.scale.o(1));
            context.rotate(that.orientation);

            that.transforms['pos'].invoke('draw', context);

            context.restore();
        }

        if (that.transforms['screen']) {
            context.save();

            that.transforms['screen'].invoke('draw', context);

            context.restore();
        }

        that.postdraw(context);
    };

    var mouseEvent = function(event, mouse) {
        mouse.inside.each(function(mote) {
            mote['mouse'+event](mouse);
        });

        return that;
    };

    var mouseDown = function(e) {
        mouse.down = true;
        mouseEvent('Down', mouse);

        that.down(mouse);
    };

    var mouseUp = function(e) {
        mouse.down = false;
        mouseEvent('Up', mouse);

        that.up(mouse);
    };

    var mouseClick = function(e) {
        mouseEvent('Click', mouse);
    };

    var mouseMove = function(e) {
        var scrollX = window.scrollX != null ? window.scrollX : window.pageXOffset;
        var scrollY = window.scrollY != null ? window.scrollY : window.pageYOffset;

        var x = (e.clientX - canvas.offsetLeft + scrollX);
        var y = (e.clientY - canvas.offsetTop + scrollY);

        mouse.prevscreen = mouse.screen;
        mouse.screen = $V([x, y]);

        mouse.prevpos = mouse.pos;
        mouse.pos = mouse.posify(mouse.screen);

        // sort out which motes are no longer under the mouse
        // and which still contain it
        if (mouse.inside.length > 0) {
            var motion = mouse.inside.partition(function(mote) {
                return mote.contains(mouse[mote.transform]);
            });

            mouse.inside = motion[0];
            mouse.inside.each(function(mote) {
                mote.mouseMove(mouse);
            });
            motion[1].each(function(mote) {
                mote.mouseOut(mouse);
            });
        }

        // find out which motes are newly under the mouse
        that.motes.each(function(mote) {
            mote.findIn(mouse, mouse[mote.transform]);
        });

        // call custom mouse move function, if one is defined
        that.move(mouse);
    };

    // parse the mouse wheel event and call wheel with a useful value
    var readDeltas = function(e) {
        var delta = 0;
        if (!e) {
            e = window.event;
        }
        if (e.wheelDelta) {
            delta = e.wheelDelta/120;
        } else if (e.detail) {
            delta = -e.detail/3;
        }
        if (delta) {
            that.wheel(that, delta);
        }
        if (e.preventDefault) {
            e.preventDefault();
        }

        e.returnValue = false;
    };

    var keyDown = function(e) {
        keys.predown(e.keyCode);

        if (that.preventKeys) {
            if (e.preventDefault) e.preventDefault();
            if (e.stopPropagation) e.stopPropagation();
            return false;
        }

        return true;
    };

    var keyUp = function(e) {
        keys.preup(e.keyCode);

        if (that.preventKeys) {
            if (e.preventDefault) e.preventDefault();
            if (e.stopPropagation) e.stopPropagation();
            return false;
        }

        return true;
    };

    // zoom keeping the current mouse position fixed.
    // works by finding the vector from the mouse position to the top left corner,
    // then scaling it to the new zoom factor.
    that.zoom = function(factor) {
        var buffer = mouse.pos.subtract(mouse.posify($V([0, 0]))).x(1.0/factor);

        that.scale = that.scale.x(factor);
        that.translation = that.translation.subtract(mouse.deposify(mouse.pos.subtract(buffer)));
    };

    that.init = function() {
        // resize
        var resize = function(e) {
            flux.browser.dim(window.innerWidth, window.innerHeight);
            canvas.width = flux.browser.w;
            canvas.height = flux.browser.h;

            that.resize(flux.browser);
        };
        window.onresize = resize;

        // mouse wheel
        if (window.addEventListener) {
            window.addEventListener('DOMMouseScroll', readDeltas, false);
        }
        window.onmousewheel = document.onmousewheel = readDeltas;

        // canvas
        canvas = document.getElementById ? document.getElementById(spec.id) : null;
        if (!canvas || !canvas.getContext) {
            return;
        }
        context = canvas.getContext('2d');
        CanvasTextFunctions.enable(context);

        // mouse events
        canvas.addEventListener('mousedown', mouseDown, false);
        canvas.addEventListener('mouseup', mouseUp, false);
        canvas.addEventListener('click', mouseClick, false);
        canvas.addEventListener('mousemove', mouseMove, false);

        // key events
        window.addEventListener('keydown', keyDown, false);
        window.addEventListener('keyup', keyUp, false);

        // dimensions
        flux.browser.dim(window.innerWidth, window.innerHeight);
        canvas.width = flux.browser.w;
        canvas.height = flux.browser.h;

        // provide a reference to the actual canvas object
        that.canvas = canvas;

        context.strokeStyle = 'rgba(0, 0, 0, 1)';
        context.lineWidth = 5;

        // timer
        setInterval(update, 20);
    };

    return that;
};


//  that.shape = spec.shape || [$V([-20, 0]), $V([20, 20]), $V([30, -10]), $V([-20, -20])];
//  that.shape = spec.shape || [$V([0, 0]), $V([100, 10]), $V([200, -10])];
