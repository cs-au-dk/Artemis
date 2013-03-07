var homeostasis = function(id) {
    var above = flux.bounds(-1700, 1700, -450, 250);
    var below = flux.bounds(-1700, 1700, 1700, 2400);
    var all = above.copy().union(below);

    var receptorGrip = 0.996;
    var attractantRepellentRatio = 0.5;
    var phosphorylationCycles = 50;
    var globalVelocity = 5;
    var timeZoom = 10;
    var dragging = false;
    var showingState = false;

    var defaultRotation = function() {return Math.random() * 0.1 - 0.05;};

    var descriptions = {
        homeostasis: 'Homeostasis is the process of maintaining some kind of balance\n'
            + 'in the face of endlessly changing external forces.  In this case\n'
            + 'the cell is always seeking to climb the gradient of attractants\n'
            + 'and oppose the gradient of repellents, leading it to sources of food\n'
            + 'and away from potentially harmful agents.  The system maintains\n'
            + 'its sensitivity to even the most subtle gradient while compensating\n'
            + 'for any saturation of either attractants or repellents in the\n'
            + 'surrounding environment.',
        about: 'This is an interactive model of cellular chemotaxis.  You can drag\n'
            + 'the model around with the mouse and zoom in and out with the scroll wheel,\n'
            + 'or the \'i\' and \'o\' keys (for \'in\' and \'out\') if you are missing a scroll wheel.\n'
            + 'Mousing over one of the components will highlight the corresponding entry\n'
            + 'in the menu, and clicking will bring up a description of that component\n'
            + 'and its role in the process of sensing chemical gradients.',
        '______________________________': 'This is the divider!',
        membrane: 'The membrane is the enclosing surface that separates\n'
            + 'the inside of the cell from the outside.  The cell\n'
            + 'maintains an electric potential across this membrane\n'
            + 'and then harnesses that potential to do work.',
        flagella: 'When the flagella spin in one direction the cell is\n'
            + 'propelled forward.  In the other direction, the cell tumbles\n'
            + 'erratically.  Because of the chemotaxis system, the cell will\n'
            + 'travel forwards mostly, and tumble infrequently, unless in the\n'
            + 'presence of repellents, where it\'s tendency to tumble will\n'
            + 'lead it away from the potentially harmful source.',
        column: 'The column spans the membrane, allowing for communication\n'
            + 'across the otherwise impenetrable barrier.  This way also\n'
            + 'transportation of materials across the membrane is strictly\n'
            + 'controlled.  In this case, receptors in the outer portion\n'
            + 'of the column bind either attractants or repellents, which\n'
            + 'act as ligands, and the inner portion is bound to cheW,\n'
            + 'which can be activated or deactived based on which ligands\n'
            + 'the outer portion is bound to.',
        repellent: 'Repellents bind to receptors in a column and\n'
            + 'increase the activity of cheW, leading to the phosphorylation\n'
            + 'of cheY and cheB.',
        attractant: 'Attractants bind to receptors in a column and\n'
            + 'reduce the activity of cheW.',
        cheW: 'cheW is activated by repellents binding to the outer portion\n'
            + 'of the column and deactivated by the binding of attractants,\n'
            + 'with its sensitivity guided by the number of bound\n'
            + 'methyl groups attached to the inner portion.  When active, cheW\n'
            + 'enables the phosphorylation of cheY, which triggers activation of the\n'
            + 'flagellar motors, and of cheB, which removes\n'
            + 'methyl groups from the column.',
        phosphate: 'Phosphate groups often act as a tag, or a signal that some condition is present.\n'
            + 'In the process of binding to various enzymes they trigger conformational\n'
            + 'changes which expose the enzymes\' active sites.  These active sites\n'
            + 'then trigger some other change, such as splicing or fusing other molecular components.',
        cheY: 'cheY is an enzyme that when phosphorylated binds to flagellar motors,\n'
            + 'inducing them to reverse their rotation and send the cell tumbling in a different direction.\n'
            + 'Most of the time the flagella are rotating in a clockwise direction, which sends\n'
            + 'the cell travelling in mostly a straight line.  The motor can be reversed, causing the cell\n'
            + 'to tumble more or less randomly, which then travels off in a new direction.',
        cheZ: 'cheZ removes phosphate groups from cheY.  In this way,\n'
            + 'a balance is struck between the phosphorylation caused by the activation of\n'
            + 'cheW when the cell is in the presence of repellents, and the steady dephosphorylation\n'
            + 'that results from interactions with cheZ.  This self-limiting cycle\n'
            + 'results in a sensitivity to chemical gradients, with the cell avoiding repellents\n'
            + 'and seeking attractants.',
        methyl: 'Methyl groups are signifiers like phosphates, and are attached to various molecules\n'
            + 'in order to induce conformational changes.  In this case, the methyls are binding\n'
            + 'to the inner portion of the columns.  The more methyl groups bound to the column,\n'
            + 'the more sensitive the column is to repellents, and the more active cheW will be.',
        cheB: 'cheB is phosphorylated in the presence of active cheW, just like cheY.  cheB\n'
            + 'removes methyl groups from columns, thereby reducing the activity of cheW and\n'
            + 'the subsequent phosphorylation of cheB (and cheY).  So here we see another layer\n'
            + 'of self-limitation, the activation of cheW leading to the phosphorylation of cheB\n'
            + 'leading to the demethylation of columns leading to the DE-activation of cheW.\n'
            + 'So the activation of cheW entails the eventual deactivation of cheW, cleaning up\n'
            + 'its own mess so to speak.  This process is called *adaptation*, and is common\n'
            + 'to a mind-boggling cross-section of biological processes.  ',
        cheR: 'cheR adds methyl groups to the inner portion of a column at a\n'
            + 'steady rate.  In this way the rate of cheW activation is steadily\n'
            + 'increased, offset by the concentration of phosphorylated cheB.\n'
            + 'This adaptive cycle of methylation and demethylation is on a much\n'
            + 'longer time-scale than the activation of cheW by repellents and\n'
            + 'the phosphorylation of cheY.  In this way the cell can be\n'
            + 'immediately responsive while at the same time adaptive to the\n'
            + 'general fluctuations of attractants and repellents in the\n'
            + 'surrounding environment.'
    };

    var molecule = function(spec) {
        var that = flux.mote(spec);
        var oldVelocity = that.velocity;

        that.neighbors = [that];

        that.state = 'base';
        that.base = function(env) {};

        that.focus = function() {
            that.oldColor = that.color.dup();
            that.tweenColor($V([255, 255, 255, 1]), 5);

            that.pause();
        };

        that.unfocus = function() {
            if (that.oldColor) that.tweenColor(that.oldColor, 5);
            that.unpause();
        };

        that.mouseIn = spec.mouseIn || function(mouse) {
            that.focus();

            if (that.type) {
                moleculeKey.itemhash[that.type].activate();
            }
        };

        that.mouseOut = spec.mouseOut || function(mouse) {
            that.unfocus();

            if (that.type) {
                moleculeKey.itemhash[that.type].deactivate();
            }
        };

        that.keyItem = function() {
            return moleculeKey.itemhash[that.type];
        };

        var showDescription = function(mouse) {
            // only show the deepest submote under the mouse
            var lowest = mouse.inside.inject(that, function(lowest, inside) {
                return lowest.supermotes().length < inside.supermotes().length ? inside : lowest;
            });

            if (that === lowest) {
//                var output = that.type + ' -- ' + that.state + '\n' + that.shape.ops.map(function(s) {return s.to.elements.map(function(x){return Math.round(x);});}) + '\n\n';

                var state = showingState ? ' -- ' + that.state : '';
                var output = that.type + state + '\n\n';
                that.keyItem().showDescription(output);
            }
        };

        var hideDescription = function(mouse) {
            that.keyItem().hideDescription(true);
        };

        that.findNeighbor = function(condition) {
            var index = 0;
            var neighbor = null;
            var found = null;

            while (!found && index < that.neighbors.length) {
                neighbor = that.neighbors[index];
                if (condition(neighbor)) {
                    found = neighbor;
                }

                index += 1;
            }

            return found;
        };

        that.perceive = spec.perceive || function(env) {
            that[that.state](env);
        };

        that.mouseDown = spec.mouseDown || showDescription;
        that.mouseUp = spec.mouseUp || hideDescription;

        return that;
    };

    var randomPos = function(box) {
        return $V(box.randomPoint());
    };

    var randomLigand = function() {
        var up = (Math.random() - 0.5) > 0;
        var inside = up ? above : below;

        if (Math.random() * (attractantRepellentRatio + 1) < attractantRepellentRatio) {
            return {type: 'attractant', ligand: attractant({pos: randomPos(inside)})};
        } else {
            return {type: 'repellent', ligand: repellent({pos: randomPos(inside)})};
        }
    };

    var randomColumn = function(box, adjustment) {
        var up = (Math.random() - 0.5) > 0;
        var x = box.randomPoint()[0] * 0.6;
        var y = up ? box[1][0] - 20 : box[1][1] + 20;
        var orientation = up ? 0 : Math.PI;

        return column({pos: $V([x, y]), orientation: orientation + adjustment});
    };

    var randomMolecule = function(type, box) {
        return type({pos: randomPos(box), bounds: box});
    };

    var ligand = function(spec) {
        var that = molecule(spec);
        var velocityScale = 0.9;

        that.closestReceptor = null;
        that.attached = false;
        that.detached = false;

        that.polarity = -1;
        that.state = 'unattached';

        that.unattached = function(env) {
            if (!exists(that.closestReceptor) || that.closestReceptor.taken) {
                that.closestReceptor = that.findClosest(membranes.first().receptors, function(receptor) {
                    return receptor.taken === false;
                });
            }

            if (exists(that.closestReceptor)) {
                var distance = that.closestReceptor.distance(that);

                if (distance > globalVelocity) {
                    that.future.append(function(self) {
                        that.velocity = that.velocity.add(that.to(that.closestReceptor).x(20/(distance))).scaleTo(velocityScale*globalVelocity);
                    });
                } else {
                    that.future.append(function(self) {
                        that.velocity = $V([0, 0]);
                        that.rotation = 0;
                    });

                    that.closestReceptor.take(that);
                    that.state = 'attached';
                }
            }
        };

        that.attached = function(env) {
            if (Math.random() > receptorGrip) {
                that.velocity = that.absolute().subtract(that.closestReceptor.column.absolute()).scaleTo(globalVelocity);
                that.rotation = defaultRotation();

                that.state = 'detached';
                that.closestReceptor.release();
                that.closestReceptor = null;
            }
        };

        that.detached = function(env) {
            if (!all.inside(that.absolute())) {
                var realm = Math.random() - 0.5 < 0 ? above : below;
                that.pos = randomPos(realm);
                that.state = 'unattached';
            }
        };

        return that;
    };

    var attractant = function(spec) {
        spec.type = 'attractant';
        spec.color = spec.color || $V([140, 170, 100, 1]);
        spec.shape = spec.shape || flux.shape({ops: [{op: 'arc', radius: 7}]});
        spec.velocity = $V([Math.random()-0.5, Math.random()-0.5]).x(globalVelocity);

        var that = ligand(spec);

        return that;
    };

    var repellent = function(spec) {
        spec.type = 'repellent';
        spec.color = spec.color || $V([170, 70, 60, 1]);
        spec.shape = spec.shape || flux.shape({ops: [
            {op: 'move', to: $V([-6, -6])},
            {op: 'line', to: $V([6, -6])},
            {op: 'line', to: $V([6, 6])},
            {op: 'line', to: $V([-6, 6])}
        ]});
        spec.rotation = defaultRotation();
        spec.velocity = $V([Math.random()-0.5, Math.random()-0.5]).x(globalVelocity);

        var that = ligand(spec);
        that.polarity = 1;

        return that;
    };

    var membrane = function(spec) {
        spec.type = 'membrane';
        spec.fill = 'stroke';
        spec.lineWidth = 30;
        spec.color = spec.color || $V([80, 20, 20, 1]);
        spec.shape = spec.shape || flux.shape({ops: [
            {op: 'move', to: $V([-1400, -700])},
            {op: 'line', to: $V([1400, -700])},
            {op: 'bezier', to: $V([1400, 700]), control1: $V([2450, -700]), control2: $V([2450, 700])},
            {op: 'line', to: $V([-1400, 700])},
            {op: 'bezier', to: $V([-1400, -700]), control1: $V([-2450, 700]), control2: $V([-2450, -700])}
        ], fill: 'stroke'});

//        spec.orientation = Math.random() * Math.PI;

        var that = molecule(spec);

        var inside = flux.bounds(that.box[0][0] + 700, that.box[0][1] - 700, that.box[1][0] + 50, that.box[1][1] - 50);

        that.columns = $R(0, 12).map(function(index) {
            return randomColumn(that.box, that.orientation);
        });

        // receptors and cheWs are part of columns, but we make a reference for them here
        that.receptors = that.columns.inject([], function(rs, column) {return rs.concat(column.receptors);});
        that.cheWs = that.columns.map(function(column) {return column.cheW;});

//         that.flagella = flagella({pos: $V([2190, 0]), orientation: that.orientation});
//         that.attach(that.flagella);

        that.phosphates = $R(0, 20).map(function(index) {
            return randomMolecule(phosphate, inside);
        });

        that.methyls = $R(0, 20).map(function(index) {
            return randomMolecule(methyl, inside);
        });

        that.cheYs = $R(0, 10).map(function(index) {
            return randomMolecule(cheY, inside);
        });

        that.cheBs = $R(0, 10).map(function(index) {
            return randomMolecule(cheB, inside);
        });

        that.cheZs = $R(0, 10).map(function(index) {
            return randomMolecule(cheZ, inside);
        });

        that.cheRs = $R(0, 10).map(function(index) {
            return randomMolecule(cheR, inside);
        });

        that.cheWSeekers = that.cheYs.concat(that.cheBs).concat(that.phosphates);

        that.receptors.each(function(receptor, index) {
            receptor.cheW = that.cheWs[index];
        });

        that.addSubmotes(that.columns
            .concat(that.phosphates)
            .concat(that.methyls)
            .concat(that.cheYs)
            .concat(that.cheZs)
            .concat(that.cheBs)
            .concat(that.cheRs));

//        that.submote_pantheon = that.cheWs.concat(that.submotes.clone());

        that.submote_pantheon = that.cheWs
            .concat(that.phosphates)
            .concat(that.methyls)
            .concat(that.cheYs)
            .concat(that.cheZs)
            .concat(that.cheBs)
            .concat(that.cheRs);

        that.perceive = function(env) {
            that.tree = Math.kdtree(that.submote_pantheon, 'absolute', 0);
            that.submote_pantheon.each(function(submote) {
                submote.neighbors = that.tree.nearest(submote.absolute(), 5, function(pod) {
                    return !(pod === that);
                });
            });

            that.submotes.each(function(submote) {
                submote.perceive(env);
            });
        };

        return that;
    };

    var column = function(spec) {
        spec.type = 'column';
        spec.color = spec.color || $V([60, 70, 170, 1]);
        spec.outline = spec.outline || $V([0, 0, 0, 1]);
        spec.lineWidth = 3;
        spec.shape = spec.shape || flux.shape({ops: [
            {op: 'move', to: $V([-30, -50])},
            {op: 'bezier', to: $V([30, -50]), control1: $V([-30, 0]), control2: $V([30, 0])},
            {op: 'line', to: $V([50, -50])},
            {op: 'bezier', to: $V([10, 0]), control1: $V([60, -50]), control2: $V([40, 0])},
            {op: 'line', to: $V([10, 100])},
            {op: 'line', to: $V([-10, 100])},
            {op: 'line', to: $V([-10, 0])},
            {op: 'bezier', to: $V([-50, -50]), control1: $V([-40, 0]), control2: $V([-60, -50])}
        ]});

        var that = molecule(spec);

        that.cheW = cheW({pos: $V([0, 100]), orientation: that.orientation, column: that});
        that.receptors = [
            receptor({pos: $V([0, -18]), column: that, cheW: that.cheW}),
            receptor({pos: $V([-25, -42]), column: that, cheW: that.cheW}),
            receptor({pos: $V([-17, -26]), column: that, cheW: that.cheW}),
            receptor({pos: $V([17, -26]), column: that, cheW: that.cheW}),
            receptor({pos: $V([25, -42]), column: that, cheW: that.cheW})
        ];
        that.addSubmotes([that.cheW].concat(that.receptors));

        that.level = 0;
        that.state = 'inactive';

        that.openMethylSites = [
            $V([10, 50]),
            $V([10, 70]),
            $V([-10, 70]),
            $V([-10, 50])
        ];

        that.takenMethylSites = [];

        that.claimMethylSite = function() {
            var site = that.openMethylSites.shift();
            that.takenMethylSites.push(site);

            return that.extrovert(site);
        };

        that.active = function(env) {
            if (that.level <= 0) {
                that.deactivate();
            }
        };

        that.inactive = function(env) {
            if (that.level > 0) {
                that.activate();
            }
        };

        that.activate = function() {
            that.state = 'active';
            that.cheW.activate();
        };

        that.deactivate = function() {
            that.state = 'inactive';
            that.cheW.deactivate();
        };

        return that;
    };

    var receptor = function(spec) {
        spec.type = 'receptor';
        spec.visible = false;
        spec.color = $V([0, 0, 0, 0]);
        spec.shape = flux.shape({ops: [{op: 'arc', to: $V([0, 0]), radius: 7}]});

        var that = molecule(spec);

        that.column = spec.column;
        that.cheW = spec.cheW;

        that.taken = false;
        that.ligand = null;
        that.delay = 0;

        that.take = function(ligand) {
            that.column.level += ligand.polarity;

            that.ligand = ligand;
            that.taken = true;
            that.perceive = that.bound;
        };

        that.release = function() {
            that.column.level -= that.ligand.polarity;

            that.ligand = null;
            that.taken = false;
            that.delay = 50;

            that.perceive = that.closed;
        };

        that.open = function(env) {

        };

        that.bound = function(env) {

        };

        that.closed = function(env) {
            if (that.delay < 1) {
                that.delay = 0;
                that.taken = false;
                that.perceive = that.open;
            } else {
                that.delay -= 1;
            }
        };

        that.perceive = function(env) {
            if (that.detached < 2) {
                that.detached = 0;
                that.taken = false;
            } else if (that.detached > 1) {
                that.detached = that.detached - 1;
            }
        };

        return that;
    };

    var cheW = function(spec) {
        spec.type = 'cheW';

        var activeColor = spec.activeColor || $V([210, 220, 130, 1]);
        var inactiveColor = spec.inactiveColor || $V([40, 40, 40, 1]);

        spec.color = spec.color || inactiveColor.dup();
        spec.shape = spec.shape || flux.shape({ops: [
            {op: 'move', to: $V([-30, 0])},
            {op: 'bezier', to: $V([30, 0]), control1: $V([30, 30]), control2: $V([-30, 30])},
            {op: 'bezier', to: $V([-30, 0]), control1: $V([-30, -30]), control2: $V([30, -30])}
        ]});

        var that = molecule(spec);

        that.active = false;
        that.column = spec.column;

        that.activate = function() {
            that.active = true;

            that.tweens = [];
            that.tweenColor(activeColor, 20);

            membranes.first().cheWSeekers.each(function(seeker) {
                if (seeker.activeCheW) {
                    if (seeker.distance(seeker.activeCheW) > seeker.distance(that)) {
                        seeker.activeCheW = that;
                    }
                }
            });
        };

        that.deactivate = function() {
            that.active = false;

            that.tweens = [];
            that.tweenColor(inactiveColor, 20);
        };

        return that;
    };

    var cheWSeeker = function(spec) {
        var that = molecule(spec);

        var velocityScale = 5;

        that.insideRadius = spec.insideRadius || 300;
        that.tooCloseRadius = spec.tooCloseRadius || 20;

        that.nearestPhosphate = null;
        that.phosphate = null;
        that.activeCheW = null;

        that.outsideCheW = function() {};
        that.insideCheW = function() {};
        that.tooCloseCheW = function() {};

        that.bound = function(env) {};

        that.state = 'identifying';

        that.switchedOff = function() {
            that.future.append(function(self) {
                that.velocity = $V([(Math.random()-0.5)*velocityScale, (Math.random()-0.5)*velocityScale]);
            });
            that.state = 'identifying';
        };

        that.identifying = function(env) {
            that.activeCheW = that.findNeighbor(function(neighbor) {
                return neighbor.type === 'cheW' && neighbor.active;
            });

            if (that.activeCheW) {
                that.orient();
                that.perceive(env);
            }
        };

        that.orient = function() {
            if (!that.activeCheW.active) {
                that.switchedOff();
            } else {
                var distance = that.distance(that.activeCheW);

                if (distance > that.insideRadius) {
                    that.state = 'outside';
                } else if (distance > that.tooCloseRadius) {
                    that.state = 'inside';
                } else {
                    that.state = 'tooClose';
                }
            }
        };

        that.outside = function(env) {
            that.orient();

            var distance = that.distance(that.activeCheW);
            var turning = that.to(that.activeCheW).x(0.2/(distance));

            that.future.append(function(self) {
                that.velocity = that.velocity.add(turning).scaleTo(velocityScale/3);
            });

            that.outsideCheW();
        };

        that.inside = function(env) {
            that.orient();

            var distance = that.distance(that.activeCheW);
            var turning = that.to(that.activeCheW).x(0.2/(distance));

            that.future.append(function(self) {
                that.velocity = that.velocity.add(turning).scaleTo(velocityScale*0.5);
            });

            that.insideCheW();
        };

        that.tooClose = function(self) {
            that.orient();

            var distance = that.distance(that.activeCheW);

            that.future.append(function(self) {
                that.velocity = that.velocity.scaleTo(distance / 50);
            });

            that.tooCloseCheW();
        };

        return that;
    };

    var phosphate = function(spec) {
        spec.type = 'phosphate';
        spec.color = spec.color || $V([120, 80, 130, 1]);

        spec.shape = spec.shape || flux.shape({ops: [
            {op: 'move', to: $V([-10, -5])},
            {op: 'line', to: $V([10, -5])},
            {op: 'line', to: $V([10, 0])},
            {op: 'bezier', to: $V([1, 0]), control1: $V([10, 10]), control2: $V([1, 10])},
            {op: 'line', to: $V([-10, 0])}
        ]});

        spec.rotation = Math.random()*0.02-0.01;
        spec.velocity = $V([Math.random()-0.5, Math.random()-0.5]).x(globalVelocity);

        var that = cheWSeeker(spec);

        that.pull = function(enzyme) {
            if (!that.state === 'bound') {
                that.future.append(function(self) {
                    self.velocity = self.velocity.add(self.to(enzyme).scaleTo(0.2));
                });
            }
        };

        that.phosphorylate = function(enzyme) {
            that.enzyme = enzyme;
            that.pos = enzyme.introvert(that.pos);
            that.absolute.expire();

            that.tweens.append(flux.tweenV({
                obj: that,
                property: 'pos',
                to: $V([-15, 10]),
                cycles: phosphorylationCycles
            }));

            that.tweens.append(flux.tweenN({
                obj: that,
                property: 'orientation',
                to: Math.PI*0.5,
                cycles: phosphorylationCycles
            }));

            that.future = [];
            that.rotation = 0;
            that.velocity = $V([0, 0]);
//          that.neighbors = [];

            that.state = 'bound';
        };

        that.dephosphorylate = function() {
            that.rotation = defaultRotation();
            that.velocity = $V([Math.random()-0.5, Math.random()-0.5]);
            that.pos = that.enzyme.extrovert(that.pos);
            that.absolute.expire();
            that.enzyme = null;

            that.state = 'identifying';
        };

        return that;
    };

    var methyl = function(spec) {
        spec.type = 'methyl';
        spec.color = spec.color || $V([130, 110, 70, 1]);
        spec.shape = spec.shape || flux.shape({ops: [
            {op: 'move', to: $V([-5, 0])},
            {op: 'line', to: $V([6, 0])},
            {op: 'line', to: $V([13, -4])},
            {op: 'line', to: $V([19, 3])},
            {op: 'line', to: $V([13, 10])},
            {op: 'line', to: $V([6, 6])},
            {op: 'line', to: $V([-5, 6])}
        ]});

        spec.rotation = defaultRotation()*0.2;
        spec.velocity = $V([Math.random()-0.5, Math.random()-0.5]).x(globalVelocity);

        var that = molecule(spec);

        that.state = 'free';
        that.enzyme = null;

        that.bind = function(enzyme, site) {
            that.state = 'binding';
            that.enzyme = enzyme;
            that.site = site;
            that.rotation = 0;
            that.velocity = $V([0, 0]);

            that.column = that.enzyme.cheWNeighbor.column;
            var modifier = that.column.introvert(that.site).elements[0] < 0 ? Math.PI : 0;

            that.tweenPos(that.site, phosphorylationCycles*2, function() {
                that.orientation = that.column.orientation + modifier;
                that.state = 'bound';
            });
        };

        that.cut = function() {
            that.enzyme = null;
            that.site = null;
            that.column = null;
            that.rotation = defaultRotation()*0.2;
            that.velocity = $V([Math.random()-0.5, Math.random()-0.5]).x(globalVelocity);

            that.state = 'free';
        };

        that.free = function(env) {

        };

        that.binding = function(env) {

        };

        that.bound = function(env) {

        };

        return that;
    };

    var cheWActor = function(spec) {
        spec.color = spec.inactiveColor.dup();
        spec.shape = spec.inactiveShape.dup();

        var that = cheWSeeker(spec);

        that.inactiveShape = spec.inactiveShape;
        that.inactiveColor = spec.inactiveColor;
        that.activeShape = spec.activeShape;
        that.activeColor = spec.activeColor;

        var velocityScale = 3;

        that.insideCheW = function() {
            that.nearestPhosphate = that.findNeighbor(function(neighbor) {
                return neighbor.type === 'phosphate' && !(neighbor.state === 'bound');
            });

            if (exists(that.nearestPhosphate)) {
                var distance = that.distance(that.nearestPhosphate);

                if (distance < 50) {
                    that.phosphorylate(that.nearestPhosphate);
                } else {
                    that.nearestPhosphate.pull(that);
                }
            }
        };

        that.phosphorylate = function(phosph) {
            that.phosphate = phosph;
            that.attach(that.phosphate);

            that.tweenColor(that.activeColor, phosphorylationCycles);
            that.tweenShape(that.activeShape, phosphorylationCycles);

            that.phosphate.phosphorylate(that);

            that.future.append(function(self) {
                self.velocity = self.activeCheW.to(self).scaleTo(velocityScale);
            });

            that.state = 'bound';
        };

        that.hold = function() {
            that.velocity = $V([0, 0]);
            that.state = 'waiting';
        };

        that.waiting = function(env) {

        };

        that.dephosphorylate = function() {
            that.tweenColor(that.inactiveColor, phosphorylationCycles);
            that.tweenShape(that.inactiveShape, phosphorylationCycles);

            that.phosphate.dephosphorylate(that);

            that.future.append(function(self) {
                self.velocity = $V([Math.random() - 0.5, Math.random() - 0.5]).scaleTo(velocityScale);
            });

            that.detach(that.phosphate);
            that.state = 'identifying';
        };

        return that;
    };

    var cheY = function(spec) {
        spec.type = 'cheY';

        var velocityScale = 3;

        spec.activeColor = spec.activeColor || $V([150, 180, 190, 1]);
        spec.inactiveColor = spec.inactiveColor || $V([40, 58, 64, 1]);

        spec.activeShape = spec.activeShape || flux.shape({ops: [
            {op: 'move', to: $V([-20, 0])},
            {op: 'bezier', to: $V([0, 3]), control1: $V([-10, 4]), control2: $V([-10, 4])},
            {op: 'bezier', to: $V([13, 19]), control1: $V([5, 17]), control2: $V([11, 20])},
            {op: 'bezier', to: $V([5, 0]), control1: $V([11, 11]), control2: $V([11, 9])},
            {op: 'bezier', to: $V([13, -19]), control1: $V([11, -9]), control2: $V([11, -11])},
            {op: 'bezier', to: $V([0, -3]), control1: $V([11, -20]), control2: $V([5, -17])},
            {op: 'bezier', to: $V([-20, 0]), control1: $V([-10, -4]), control2: $V([-10, -4])}
        ]});

        spec.inactiveShape = spec.inactiveShape || flux.shape({ops: [
            {op: 'move', to: $V([-20, 0])},
            {op: 'bezier', to: $V([-8, 0]), control1: $V([-20, 15]), control2: $V([-0, 5])},
            {op: 'bezier', to: $V([11, 10]), control1: $V([5, 10]), control2: $V([11, 10])},
            {op: 'bezier', to: $V([20, 0]), control1: $V([20, 0]), control2: $V([20, 0])},
            {op: 'bezier', to: $V([11, -10]), control1: $V([20, -0]), control2: $V([20, -0])},
            {op: 'bezier', to: $V([-8, 0]), control1: $V([11, -10]), control2: $V([5, -10])},
            {op: 'bezier', to: $V([-20, 0]), control1: $V([-0, -5]), control2: $V([-20, -15])}
        ]});

        spec.rotation = Math.random()*0.02-0.01;
        spec.velocity = $V([Math.random()-0.5, Math.random()-0.5]).x(globalVelocity);

        var that = cheWActor(spec);
        return that;
    };

    var cheZ = function(spec) {
        spec.type = 'cheZ';
        spec.inactiveColor = spec.inactiveColor || $V([220, 30, 20, 1]);
        spec.activeColor = spec.activeColor || $V([250, 140, 50, 1]);

        spec.inactiveShape = spec.inactiveShape || flux.shape({ops: [
            {op: 'move', to: $V([-15, -15])},
            {op: 'line', to: $V([15, -15])},
            {op: 'line', to: $V([-5, 10])},
            {op: 'line', to: $V([15, 10])},
            {op: 'line', to: $V([15, 15])},
            {op: 'line', to: $V([-15, 15])},
            {op: 'line', to: $V([5, -10])},
            {op: 'line', to: $V([-15, -10])}
        ]});

        spec.activeShape = spec.activeShape || flux.shape({ops: [
            {op: 'move', to: $V([-15, -6])},
            {op: 'line', to: $V([15, -6])},
            {op: 'line', to: $V([-5, 1])},
            {op: 'line', to: $V([15, 1])},
            {op: 'line', to: $V([15, 6])},
            {op: 'line', to: $V([-15, 6])},
            {op: 'line', to: $V([5, -1])},
            {op: 'line', to: $V([-15, -1])}
        ]});

        spec.color = spec.inactiveColor.dup();
        spec.shape = spec.inactiveShape.dup();

        spec.rotation = Math.random()*0.02-0.01;
        spec.velocity = $V([Math.random()-0.5, Math.random()-0.5]).x(globalVelocity);

        var that = molecule(spec);

        that.inactiveColor = spec.inactiveColor;
        that.inactiveShape = spec.inactiveShape;
        that.activeColor = spec.activeColor;
        that.activeShape = spec.activeShape;

        that.phosphorylated = null;

        that.active = function(env) {};

        that.avoidCheW = function() {
            var cheWNeighbor = that.findNeighbor(function(neighbor) {
                return neighbor.type === 'cheW';
            });

            if (cheWNeighbor) {
                that.future.append(function(self) {
                    that.velocity = that.velocity.subtract(that.to(cheWNeighbor)).scaleTo(globalVelocity);
                });
            }

            return cheWNeighbor;
        };

        that.seek = function(env) {
            var cheWNeighbor = that.avoidCheW();
            if (cheWNeighbor) {

            } else {
                that.phosphorylated = that.findNeighbor(function(neighbor) {
                    return neighbor.type === 'phosphate' && neighbor.enzyme ;
                });

                if (that.phosphorylated) {
                    that.state = 'target';
                }
            }
        };

        that.target = function(env) {
            var cheWNeighbor = that.avoidCheW();
            if (cheWNeighbor) {

            } else if (!that.phosphorylated.enzyme || that.phosphorylated.enzyme.state === 'waiting') {
                that.phosphorylated = null;
                that.state = 'seek';
            } else {
                var distance = that.distance(that.phosphorylated);

                if (distance < 20) {
                    that.state = 'cut';
                    that.perceive(env);
                } else {
                    that.future.append(function(self) {
                        that.velocity = that.velocity.add(that.to(that.phosphorylated)).scaleTo(globalVelocity);
                    });
                }
            }
        };

        that.cut = function(env) {
            that.tweenShape(that.activeShape, phosphorylationCycles/5);
            that.tweenColor(that.activeColor, phosphorylationCycles/5);
            that.tweenEvent(function() {that.state = 'uncut';}, phosphorylationCycles/5);
            that.velocity = $V([0, 0]);
            that.future = [];

            that.phosphorylated.enzyme.hold();

            that.state = 'active';
        };

        that.uncut = function() {
            if (that.phosphorylated) {
                that.phosphorylated.enzyme.dephosphorylate();

                that.tweenShape(that.inactiveShape, phosphorylationCycles);
                that.tweenColor(that.inactiveColor, phosphorylationCycles);
                that.velocity = $V([Math.random() - 0.5, Math.random() - 0.5]).scaleTo(globalVelocity);

                that.phosphorylated = null;
                that.state = 'seek';
            }
        };

        that.state = 'seek';
        return that;
    };

    var cheB = function(spec) {
        spec.type = 'cheB';

        spec.activeColor = spec.activeColor || $V([100, 140, 230, 1]);
        spec.inactiveColor = spec.inactiveColor || $V([80, 80, 90, 1]);

        spec.inactiveShape = spec.inactiveShape || flux.shape({ops: [
            {op: 'move', to: $V([-15, -15])},
            {op: 'line', to: $V([0, -15])},
            {op: 'line', to: $V([15, -15])},
            {op: 'bezier', to: $V([0, -5]), control1: $V([15, 15]), control2: $V([0, 15])},
            {op: 'bezier', to: $V([-15, -15]), control1: $V([0, 15]), control2: $V([-15, 15])}
        ]});

        spec.activeShape = spec.activeShape || flux.shape({ops: [
            {op: 'move', to: $V([-11, -25])},
            {op: 'line', to: $V([0, -12])},
            {op: 'line', to: $V([11, -25])},
            {op: 'bezier', to: $V([0, -5]), control1: $V([25, -16]), control2: $V([30, 25])},
            {op: 'bezier', to: $V([-11, -25]), control1: $V([-30, 25]), control2: $V([-25, -16])}
        ]});

        spec.rotation = Math.random()*0.02-0.01;
        spec.velocity = $V([Math.random()-0.5, Math.random()-0.5]).x(globalVelocity);

        var that = cheWActor(spec);

        that.bound = function(env) {
            that.methylNeighbor = that.findNeighbor(function(neighbor) {
                return neighbor.type === 'methyl' && neighbor.state === 'bound' && neighbor.column.state === 'active' && (neighbor.column != that.lastColumn);
            });

            if (that.methylNeighbor) {
                that.state = 'targeting';
                that.column = methylNeighbor.column;
            }
        };

        that.targeting = function(env) {
            if (that.methylNeighbor.column.state === 'inactive') {
                that.methylNeighbor = null;
                that.state = 'bound';
            } else if (that.distance(that.methylNeighbor) < 30) {
                that.methylNeighbor.cut();
                that.state = 'bound';
                that.lastColumn = that.column;
                that.column = null;
            } else {
                that.future.append(function(self) {
                    self.velocity = self.to(self.methylNeighbor).scaleTo(5);
                });
            }
        };

        return that;
    };

    var cheR = function(spec) {
        spec.type = 'cheR';
        spec.color = spec.color || $V([180, 180, 220, 1]);

        spec.shape = spec.shape || flux.shape({ops: [
            {op: 'move', to: $V([-15, -15])},
            {op: 'line', to: $V([15, -15])},
            {op: 'line', to: $V([15, -10])},
            {op: 'bezier', to: $V([0, -5]), control1: $V([15, 15]), control2: $V([0, 15])},
            {op: 'line', to: $V([-10, -5])},
            {op: 'line', to: $V([-10, 15])},
            {op: 'line', to: $V([-15, 15])}
        ]});

        spec.rotation = Math.random()*0.02-0.01;
        spec.velocity = $V([Math.random()-0.5, Math.random()-0.5]).x(globalVelocity);

        var that = molecule(spec);

        that.methylNeighbor = null;
        that.cheWNeighbor = null;
        that.lastCheW = null;
        that.state = 'looking';

        that.looking = function(env) {
            that.methylNeighbor = that.findNeighbor(function(neighbor) {
                return neighbor.type === 'methyl' && neighbor.state === 'free';
            });
            that.cheWNeighbor = that.findNeighbor(function(neighbor) {
                return neighbor.type === 'cheW' && (neighbor != that.lastCheW);
            });

            if (that.methylNeighbor && that.cheWNeighbor && that.cheWNeighbor.column.openMethylSites.length > 0) {
                var column = that.cheWNeighbor.column;

                that.targetSite = column.claimMethylSite();
                that.methylNeighbor.bind(that, that.targetSite);
                that.velocity = $V([0, 0]);

                that.tweenPos(column.extrovert(that.cheWNeighbor.pos), phosphorylationCycles*2, function() {
                    that.state = 'looking';
                    that.future.append(function() {
                        that.velocity = $V([Math.random()-0.5, Math.random()-0.5]).scaleTo(globalVelocity);
                    });
                });
                that.lastCheW = that.cheWNeighbor;
                that.methylNeighbor = null;
                that.cheWNeighbor = null;

                that.state = 'binding';
            }
        };

        that.binding = function(env) {

        };

        return that;
    };

    var flagella = function(spec) {
        spec.type = 'flagella';
//        spec.color = spec.color || $V([60, 70, 170, 1]);
        spec.color = spec.color || $V([20, 30, 70, 1]);

        spec.revertingshape = spec.shape || flux.shape({ops: [
            {op: 'move', to: $V([-50, -110])},
            {op: 'line', to: $V([30, -100])},
            {op: 'line', to: $V([30, -40])},
            {op: 'line', to: $V([60, -40])},
            {op: 'line', to: $V([60, -70])},
            {op: 'bezier', to: $V([1100, -10]), control1: $V([400, -270]), control2: $V([700, -250])},
            {op: 'bezier', to: $V([2700, -60]), control1: $V([1700, 260]), control2: $V([2200, 260])},
            {op: 'bezier', to: $V([3400, 0]), control1: $V([2900, -180]), control2: $V([3000, -150])},
            {op: 'bezier', to: $V([2700, 50]), control1: $V([3000, -80]), control2: $V([2900, -80])},
            {op: 'bezier', to: $V([1100, 150]), control1: $V([2300, 370]), control2: $V([1700, 370])},
            {op: 'bezier', to: $V([60, 100]), control1: $V([700, -70]), control2: $V([400, -40])},
            {op: 'line', to: $V([60, 40])},
            {op: 'line', to: $V([30, 40])},
            {op: 'line', to: $V([30, 100])},
            {op: 'line', to: $V([-50, 110])}
        ]});

        spec.waxingshape = flux.shape({ops: [
            {op: 'move', to: $V([-50, -110])},
            {op: 'line', to: $V([30, -100])},
            {op: 'line', to: $V([30, -40])},
            {op: 'line', to: $V([60, -40])},
            {op: 'line', to: $V([60, -70])},
            {op: 'bezier', to: $V([1100, -50]), control1: $V([400, -80]), control2: $V([700, -80])},
            {op: 'bezier', to: $V([2700, -40]), control1: $V([1700, 10]), control2: $V([2200, 10])},
            {op: 'bezier', to: $V([3400, -30]), control1: $V([2900, -60]), control2: $V([3000, -50])},
            {op: 'bezier', to: $V([2700, 30]), control1: $V([3000, 60]), control2: $V([2900, 80])},
            {op: 'bezier', to: $V([1100, 40]), control1: $V([2300, 20]), control2: $V([1700, 30])},
            {op: 'bezier', to: $V([60, 50]), control1: $V([700, 80]), control2: $V([400, 80])},
            {op: 'line', to: $V([60, 40])},
            {op: 'line', to: $V([30, 40])},
            {op: 'line', to: $V([30, 100])},
            {op: 'line', to: $V([-50, 110])}
        ]});

        spec.invertingshape = flux.shape({ops: [
            {op: 'move', to: $V([-50, -110])},
            {op: 'line', to: $V([30, -100])},
            {op: 'line', to: $V([30, -40])},
            {op: 'line', to: $V([60, -40])},
            {op: 'line', to: $V([60, -70])},
            {op: 'bezier', to: $V([1100, 10]), control1: $V([400, 270]), control2: $V([700, 250])},
            {op: 'bezier', to: $V([2700, 60]), control1: $V([1700, -260]), control2: $V([2200, -260])},
            {op: 'bezier', to: $V([3400, 0]), control1: $V([2900, 180]), control2: $V([3000, 150])},
            {op: 'bezier', to: $V([2700, -50]), control1: $V([3000, 80]), control2: $V([2900, 80])},
            {op: 'bezier', to: $V([1100, -150]), control1: $V([2300, -370]), control2: $V([1700, -370])},
            {op: 'bezier', to: $V([60, -100]), control1: $V([700, 70]), control2: $V([400, 40])},
            {op: 'line', to: $V([60, 40])},
            {op: 'line', to: $V([30, 40])},
            {op: 'line', to: $V([30, 100])},
            {op: 'line', to: $V([-50, 110])}
        ]});

        spec.waningshape = flux.shape({ops: [
            {op: 'move', to: $V([-50, -110])},
            {op: 'line', to: $V([30, -100])},
            {op: 'line', to: $V([30, -40])},
            {op: 'line', to: $V([60, -40])},
            {op: 'line', to: $V([60, -70])},
            {op: 'bezier', to: $V([1100, 50]), control1: $V([400, 20]), control2: $V([700, 10])},
            {op: 'bezier', to: $V([2700, 40]), control1: $V([1700, 80]), control2: $V([2200, 90])},
            {op: 'bezier', to: $V([3400, 30]), control1: $V([2900, 0]), control2: $V([3000, 10])},
            {op: 'bezier', to: $V([2700, -30]), control1: $V([3000, 0]), control2: $V([2900, 0])},
            {op: 'bezier', to: $V([1100, -40]), control1: $V([2300, -90]), control2: $V([1700, -80])},
            {op: 'bezier', to: $V([60, 50]), control1: $V([700, -10]), control2: $V([400, -20])},
            {op: 'line', to: $V([60, 40])},
            {op: 'line', to: $V([30, 40])},
            {op: 'line', to: $V([30, 100])},
            {op: 'line', to: $V([-50, 110])}
        ]});

        spec.shape = spec.revertingshape.dup();

        var that = molecule(spec);
        var cycle = 3;
        var theta = 0;

        var phases = ['waxing', 'inverting', 'waning', 'reverting'];
        var phase = 0;

        that.state = phases[phase];
        that.tweenShape(spec[that.state + 'shape'], cycle);

        that.statemaker = function(symbol) {
            var state = function(env) {
                if (theta < cycle) {
                    theta += 1;
                } else {
                    phase += 1;
                    if (phase >= phases.length) {
                        phase = 0;
                    }

                    that.state = symbol;
                    that.tweenShape(spec[that.state + 'shape'], cycle);
                    theta = 0;
                }
            };

            return state;
        };

        var index = 0;
        phases.each(function(p) {
            index += 1;
            var next = phases[index % phases.length];
            that[p] = that.statemaker(next);
        });

        return that;
    };

    var ligands = {
        attractant: [],
        repellent: []
    };

    $R(0, 30).map(function(index) {
        var one = randomLigand();
        ligands[one.type].append(one.ligand);
    });

    var membranes = [membrane({pos: $V([0, 985]), orientation: 0})];

    var visible = {
        ligand: ligands,
        membrane: membranes
    };

    var focusGroups = [
        {name: 'membrane', path: 'membrane'},
        {name: 'column', path: 'membrane.0.columns'},
//        {name: 'flagella', path: 'membrane.0.flagella'},
        {name: 'repellent', path: 'ligand.repellent'},
        {name: 'attractant', path: 'ligand.attractant'},
        {name: 'cheW', path: 'membrane.0.cheWs'},
        {name: 'phosphate', path: 'membrane.0.phosphates'},
        {name: 'cheY', path: 'membrane.0.cheYs'},
        {name: 'cheZ', path: 'membrane.0.cheZs'},
        {name: 'methyl', path: 'membrane.0.methyls'},
        {name: 'cheB', path: 'membrane.0.cheBs'},
        {name: 'cheR', path: 'membrane.0.cheRs'}
    ];

    focusGroups.arrange = function() {
        // arrange the descriptions in a circle
        var wedge = Math.PI*2*(1.0/focusGroups.length);
        var third = Math.PI*2.0/3;
        var outwards = $V([0.42, 0.22]);
        var zero = $V([0, 0]);
        var center = $V([0.245, 0.26]);

        $V([250, 240, 30, 1]);

        var colorWheel = function(phase) {
            return Math.floor(140 + (Math.sin(phase)*60));
        };

        focusGroups.each(function(group, index) {
            var around = wedge*index;
            var color = [around, around+(2*third), around+third].map(function(phase) {
                return colorWheel(phase);
            });
            color.append(1);

            group.outer = outwards.rotate(around, center).times($V([1, 1.7]));
            group.descriptionColor = $V(color);
        });
    };
    focusGroups.arrange();

    // descriptive menu -------------

    var moleculeFocus = function(group) {

    };

    var moleculeKey = function() {
        var keyspec = {
            pos: $V([0.72, 0.1]),
            shape: flux.shape({ops: [
                {op: 'move', to: $V([0, 0])},
                {op: 'line', to: $V([200, 0])},
                {op: 'line', to: $V([200, 410])},
                {op: 'line', to: $V([0, 410])}
            ]}),
            orientation: 0,
            lineWidth: 2,
            outline: $V([170, 170, 170, 1]),
            color: $V([0, 0, 0, 1]),
            transform: 'screen'
        };
        var key = flux.mote(keyspec);

        var description = function(spec) {
            spec.orientation = 0;
            spec.fill = 'stroke';
            spec.lineWidth = 2;
            spec.transform = 'screen';

            var desc = flux.mote(spec);

            desc.setDescription = function(description) {
                var text = desc.findText(description);
                var background = text.box.scale(1.1).shapeFor();
                background.color = $V([20, 20, 20, 1]);

                desc.description = description;
                desc.shapes = [background, text];
                desc.findBox();
            };

            desc.findText = function(string) {
                var ops = string.split('\n').map(function(line, index) {
                    return {op: 'text', to: desc.pos.add($V([0, index*23])), size: 12, string: line};
                });

                return flux.shape({ops: ops, fill: 'stroke'});
            };

            desc.setDescription(spec.description);
            desc.item = spec.item;
            desc.mouseDown = desc.item.hideDescription;

            return desc;
        };

        var keyitem = function(spec) {
            var inactiveColor = spec.inactiveColor || $V([110, 130, 210, 1]);
            var activeColor = $V([230, 230, 230, 1]);

            spec.color = spec.color || inactiveColor.dup();
            spec.orientation = 0;
            spec.fill = 'stroke';
            spec.shape = spec.shape || flux.shape({ops: [
                {op: 'text', to: $V([0, 0]), size: 14, string: spec.name}
            ], fill: 'stroke'});

            var item = flux.mote(spec);

            item.name = spec.name;
            item.path = spec.path;

            item.active = false;
            item.outer = spec.outer || $V([5000, 0]);
            item.descriptionColor = spec.descriptionColor || $V([250, 240, 30, 1]);
            item.description = description({
                item: item,
                pos: item.outer,
                color: item.descriptionColor,
                description: descriptions[item.name] || ''
            });

            item.changeText = function(text) {
                item.shapes = [flux.shape({ops: [
                    {op: 'text', to: $V([0, 0]), size: 14, string: text}
                ], fill: 'stroke'})];
            };

            item.activate = function() {
                if (!item.active) {
                    item.tweens = [];
                    item.tweenColor(activeColor, 3);
                    item.tweenScale($V([1.05, 1.05]), 3);

                    item.active = true;
                }
            };

            item.deactivate = function() {
                if (item.active) {
                    item.tweens = [];
                    item.tweenColor(inactiveColor, 3);
                    item.tweenScale($V([1, 1]), 3);

                    item.active = false;
                }
            };

            item.showDescription = function(info) {
                if (info) {
                    item.description.setDescription(info + descriptions[item.name]);
                }
                world.addActiveDescription(item.description);
            };

            item.hideDescription = function(info) {
                if (info) {
                    item.description.setDescription(descriptions[item.name]);
                }
                world.removeActiveDescription();
            };

            item.mouseDownDescription = function() {
                item.showDescription();
            };

            item.mouseUpDescription = function() {
                item.hideDescription();
            };

            if (!spec.inactive) {
                item.mouseIn = item.activate;
                item.mouseOut = item.deactivate;
                item.mouseDown = item.mouseDownDescription;
                item.mouseUp = item.mouseUpDescription;
            }

            return item;
        };

        var homeostatic = keyitem({
            name: 'homeostasis',
            pos: $V([10, 20]),
            outer: $V([0.2, 0.05]),
            inactiveColor: $V([150, 150, 110, 1]),
            descriptionColor: $V([240, 230, 170, 1])
        });

        var about = keyitem({
            name: 'about',
            pos: $V([10, 50]),
            outer: $V([0.2, 0.7]),
            inactiveColor: $V([150, 150, 110, 1]),
            descriptionColor: $V([150, 150, 210, 1])
        });

        var divider = keyitem({
            name: '______________________________',
            pos: $V([-35, 70]),
            outer: $V([0.5, 0.5]),
            inactive: true,
            inactiveColor: $V([210, 110, 110, 1]),
            descriptionColor: $V([150, 150, 210, 1])
        });

        divider.activate = function() {
            divider.changeText('__________________hide________');
        };

        divider.deactivate = function() {
            divider.changeText('______________________________');
        };

        var hideCycle = 7;

        divider.hide = function() {
            key.tweenPos($V([0.72, -0.9]), hideCycle);
        };

        divider.show = function() {
            key.tweenPos($V([0.72, 0.1]), hideCycle);
        };

        divider.mouseIn = divider.activate;
        divider.mouseOut = divider.deactivate;
        divider.mouseDown = divider.hide;
        divider.mouseUp = divider.hide;

        key.itemhash = {};
        key.keyitems = [homeostatic, about, divider].concat(focusGroups.map(function(group, index) {
            group.pos = $V([10, index*30+100]);
            var item = keyitem(group);

            key.itemhash[group.name] = item;
            return item;
        }));

        key.addSubmotes(key.keyitems);

        return key;
    }();

    // creation of flux canvas -------------------

    var spec = {
        id: id,
        motes: membranes.concat(ligands.attractant).concat(ligands.repellent).append(moleculeKey),
        scale: $V([0.17, 0.17]),

        translation: $V([500, 200]),
//        translation: $V([0, 200]),

        move: function(mouse) {
            if (mouse.down) {
                world.removeActiveDescription();
                this.translation = this.translation.add(mouse.screen.subtract(mouse.prevscreen));

                dragging = true;
            }
        },

        keyDown: function(that, key) {
            var base = 1.25;

            if (key == 79) {
                var scale = Math.pow(base, -1);
                that.zoom(scale);
            }
            if (key == 73) {
                var scale = Math.pow(base, 1);
                that.zoom(scale);
            }
        },

        // delta is either 1 or -1, which is the exponent of the scaling constant
        // signifying either the number or its inverse.
        wheel: function(that, delta) {
            var scale = Math.pow(1.007, delta);
            that.zoom(scale);
        }
    };

    var world = flux.canvas(spec);
    world.activeDescription = null;

    world.addActiveDescription = function(description) {
        world.removeActiveDescription();

        world.addMote(description);
        world.activeDescription = description;
    };

    world.removeActiveDescription = function() {
        if (world.activeDescription) {
            world.removeMote(world.activeDescription);
            world.activeDescription = null;
        }
    };

    // for testing
    world.membrane = membranes[0];
    world.key = moleculeKey;


    return world;
};