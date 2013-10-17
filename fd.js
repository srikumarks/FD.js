// Copyright (c) 2011, Srikumar K. S. (srikumarks@gmail.com)
// License: New BSD (http://www.opensource.org/licenses/bsd-license.php)
//
// Module: FD
// Status: Work (very much) in progress
//
// Basic finite domain constraint programming using the
// "computation spaces" idea in Oz to factorize a search
// problem into propagators, distributors, search strategies
// and problem scripts.
//
// Exports:
// 
// Class FD.space is a computation space.
// FD.space has methods that add propagators to spaces.
// Each space has a "brancher" object that can branch
// a space if it isn't solved yet and some options can be
// explored. You can enqueue different branchers into a
// space's brancher object which will then control how the
// search tree is created.
//
// Namespace FD.distribute has the following strategies -
//    FD.distribute.naive
//    FD.distribute.fail_first
// 
// Namespace FD.search has the following search algo -
//    FD.search.depth_first
//
var FD = (function (exports, Math) {

    var FD_SUP = 100000000;

    // Fails if the given dom is empty by throwing 'fail'.
    // If it isn't empty, dom itself is returned. 
    // Useful within propagators.
    function domain_non_empty(dom) {
        if (dom.length === 0) { throw 'fail'; }
        return dom;
    }

    // CSIS form = Canonical Sorted Interval Sequeunce form.
    //
    // Intersection of two domains given in CSIS form.
    // r is optional and if given it should be an array and
    // the domain pieces will be inserted into it, in which case
    // the result domain will be returned unsimplified.
    function domain_intersection(dom1, dom2, r) {
        var i, j, len1, len2, b1, b2, d1, d2, d3, d4, d, mx, mn;

        if (dom1.length === 0 || dom2.length === 0) {
            return r || [];
        }

        if (dom1.length === 1) {
            if (dom2.length === 1) {
                b1 = dom1[0];
                b2 = dom2[0];
                mn = b1[0] > b2[0] ? b1[0] : b2[0];
                mx = b1[1] < b2[1] ? b1[1] : b2[1];
                r = r || [];
                if (mx >= mn) {
                    r.push([mn, mx]);
                }
                return r;
            } else {
                return domain_intersection(dom2, dom1, r);
            }
        } else {
            if (dom2.length === 1) {
                mn = dom2[0][0];
                mx = dom2[0][1];
                r = r || [];
                for (i = 0, len1 = dom1.length; i < len1; ++i) {
                    d = dom1[i];
                    if (d[0] <= mx && d[1] >= mn) {
                        r.push([(mn > d[0] ? mn : d[0]), (mx < d[1] ? mx : d[1])]);
                    }
                }
                return r;
            } else {
                // Worst case. Both lengths are > 1. Divide and conquer. 
                i = dom1.length >> 1;
                j = dom2.length >> 1;
                d1 = dom1.slice(0, i);
                d2 = dom1.slice(i);
                d3 = dom2.slice(0, j);
                d4 = dom2.slice(j);
                d = domain_intersection(d1, d3, r);
                d = domain_intersection(d1, d4, d);
                d = domain_intersection(d2, d3, d);
                d = domain_intersection(d2, d4, d);
                return r ? d : simplify_domain(d);
            }
        }
    }

    // Turns d into CSIS form.
    function simplify_domain(d) {
        if (d.length === 0) {
            return d;
        }

        if (d.length === 1) {
            if (d[0][1] < d[0][0]) {
                return [];
            } else {
                return d;
            }
        }

        var result = [];
        var i, len, prev, prevL, prevR, next, nextL, nextR;

        // Find the first index from which we need to do the
        // simplification. If at the end of this loop i >= len,
        // then we need to do nothing and we avoid loading the GC.
        // This loop checks for overlaps and ordering issues.
        prevL = d[0][0]; prevR = d[0][1];
        i = 0; len = d.length;
        if (prevR >= prevL) {
            for (i = 1; i < len; ++i) {
                next = d[i];
                if (next[1] < next[0] || next[0] <= prevR || next[1] <= prevR) {
                    break;
                } else {
                    prevR = next[1];
                }
            }
        }

        if (i >= len) {
            // Nothing to do.
            return d;
        }

        d.sort(function (d1, d2) { return d1[0] - d2[0]; });
        result.push(prev = d[0]);

        for (i = 1, len = d.length; i < len; ++i) {
            next = d[i];
            if (prev[1] >= next[0]) {
                // Two consecutive domains that are at least touching.
                // Merge them.
                prev[1] = Math.max(prev[1], next[1]);
            } else {
                result.push(prev = next);
            }
        }

        d.splice(0, d.length);
        d.push.apply(d, result);
        return result;
    }

    function domain_bounds(d) {
        if (d.length > 0) {
            return [d[0][0], d[d.length-1][1]];
        } else {
            throw 'fail';
        }
    }

    function domain_equal(d1, d2) {
        if (d1.length != d2.length) {
            return false;
        }

        var i, len;
        for (i = 0, len = d1.length; i < len; ++i) {
            if (d1[i][0] != d2[i][0] || d1[i][1] != d2[i][1]) {
                return false;
            }
        }

        return true;
    }

    // The complement of a domain is such that domain U domain' = [[0, FD_SUP]].
    function domain_complement(d) {
        if (d.length === 0) {
            return [[0, FD_SUP]];
        } else {
            var end = 0;
            var result = [];
            var i, len;
            for (i = 0, len = d.length; i < len; ++i) {
                if (end < d[i][0]) {
                    result.push([end, d[i][0] - 1]);
                }
                end = d[0][1] + 1;
            }
            if (end < FD_SUP) {
                result.push([end, FD_SUP]);
            }
            return result;
        }
    }

    // The union of two domains contains all the intervals in either domain.
    function domain_union(d1, d2) {
        var result = [];
        result.push.apply(result, d1);
        result.push.apply(result, d2);
        return simplify_domain(result);
    }

    // If a parent 'brancher' is given, then the queue is shared
    // with the parent, but the next_brancher is incremented.
    function Brancher(S, brancher) {
        this.space = S;
        this.queue = brancher ? brancher.queue : [];
        this.next_brancher = brancher ? brancher.next_brancher : 0;
    }

    Brancher.prototype = {
        branch: function () {
            // Note that the "next brancher" field will be
            // taken from the deepest space's brancher object
            // due to access via 'this'. However, the queue
            // is an array whose contents are common to all 
            // branchers part of the same tree.
            var b, ch = null;

            do {
                b = this.queue[this.next_brancher];
                ch = b ? b.branch.call(this, this.space) : null;
            } while (ch === null && this.descend());

            return ch;
        },

        enqueue: function (b) {
            // Note that the queue is common to all spaces
            // starting from the parent space, but the
            // 'next_brancher' index is local to the brancher
            // belonging to each space.
            this.queue.push(b);
            return this;
        },

        descend: function () {
            if (this.next_brancher + 1 < this.queue.length) {
                this.next_brancher++;
                return true;
            } else {
                return false;
            }
        },

        descend_and_branch: function () {
            return this.descend() ? this.branch() : null;
        }
    };

    // Empty propagation step
    function empty_propagation_step() {
        return 0;
    }

    // A propagator is solved if all the depvars it affects and
    // depends on have domains of size = 1.
    function propagator_is_solved(S, p, dont_mark_solved) {
        var i, len, b;
        
        if (p.solved) {
            return true; 
        }

        for (i = 0, len = p.allvars.length; i < len; ++i) {
            if (S.vars[p.allvars[i]].is_undetermined()) {
                return false;
            }
        }

//        return dont_mark_solved ? true : (p.solved = true);
        return true;        
    }

    // Some common features for all propagators
    var Propagator = {
        save_vars: function (P) {
            var var_state_stack = P.var_state_stack || (P.var_state_stack = []);
            var i, N, doms = [], steps = [];
            for (i = 1, N = P.space.length; i < N; ++i) {
                doms.push(P.space[i].dom);
                steps.push(P.space[i].step);
            }
            var_state_stack.push([doms, steps, P.last_step]);     
            P.old_step = P.step;
        },

        restore_vars: function (P) {
            var vss = P.var_state_stack.pop();
            var doms = vss[0], steps = vss[1];
            var i, N;
            for (i = 1, N = P.space.length; i < N; ++i) {
                P.space[i].dom = doms[i - 1];
                P.space[i].step = steps[i - 1];
            }
            P.step = P.old_step;
            P.last_step = vss[2];
        },

        discard_saved_vars: function (P) {
            P.var_state_stack.pop();
            delete P.old_step;
        },

        snapshot_vars: function (P) {
            this.save_vars(P);
            return P.var_state_stack.pop()[0];
        },

        complementary_operator: {
            eq: 'neq',
            neq: 'eq',
            lt: 'gte',
            gt: 'lte',
            lte: 'gt',
            gte: 'lt'
        }
    };

    // Concept of a space that holds fdvars, propagators and branchers.
    function Space(S) {
        if (S) {
            // The given space is being cloned.
            var i, j, v, p;

            // Bring the fdvars in using copy-on-write.
            this.vars = {};
            for (i in S.vars) {
                p = S.vars[i];
                this.vars[i] = new FDVar(p.dom, p.step);
            }

            // The propagators can simply be borrowed by reference
            // into this space since they all have a "set space" step
            // before they get to run.
            this._propagators = [];
            for (i = 0; i < S._propagators.length; ++i) {
                p = S._propagators[i];
                if (!propagator_is_solved(S, p)) {
                    v = {allvars: p.allvars, depvars: p.depvars, step: p.step};
                    this.newprop(v);
                }
            }

            // The brancher queue object is shared with the parent,
            // except for the "next brancher" state which is made
            // local to this space.
            this.brancher = new Brancher(this, S.brancher);

            // Keep note of the space that this one was cloned from.
            //
            // TODO: Remove this reference. It might result in less
            // memory being used during searches. If we keep around the
            // parent space like this, then we have to maintain all
            // spaces that we search in memory. For now, since I'm
            // still debugging, this is all right.
            this.clone_of = S;
        } else {
            // The FDVARS are all named and accessed by name.
            // When a space is cloned, the clone's fdvars objects
            // all have their __proto__ fields set to the parent's
            // fdvars object. This gets us copy on modify semantics.
            this.vars = {};
            this._propagators = [];
            this.brancher = new Brancher(this);
        }

        this.succeeded_children = 0;
        this.failed_children = 0;
        this.stable_children = 0;

        return this;
    }

    // Duplicates the functionality of new Space(S) for readability.
    Space.prototype.clone = function () {
        return new Space(this);
    };

    // When done with the space, call this to send success results
    // to the parent space from which it was cloned.
    Space.prototype.done = function () {
        if (this.clone_of) {
            this.clone_of.succeeded_children += this.succeeded_children;
            this.clone_of.failed_children += this.failed_children;
            if (this.failed) {
                this.clone_of.failed_children++;
            }
            if (this.succeeded_children === 0 && this.failed_children > 0) {
                this.failed = true;
            }
            this.clone_of.stable_children += this.stable_children;
        }
    };

    // A monotonically increasing class-global counter for unique temporary variable names.
    Space._temp_count = 1;

    // Run all the propagators until stability point. Returns the number
    // of changes made or throws a 'fail' if any propagator failed.
    Space.prototype.propagate = function () {
        var i, ps, len, count, totalCount = 0;
        do {
            for (i = 0, ps = this._propagators, len = ps.length, count = 0; i < len; ++i) {
                count += ps[i].step();
            }
            totalCount += count;
        } while (count > 0);
        // console.log(JSON.stringify(this.solution()));
        return totalCount;
    };

    // Returns true if this space is solved - i.e. when
    // all the fdvars in the space have a singleton domain.
    //
    // This is a *very* strong condition that might not need
    // to be satisfied for a space to be considered to be
    // solved. For example, the propagators may determine
    // ranges for all variables under which all conditions
    // are met and there would be no further need to enumerate
    // those solutions.
    //
    // For weaker tests, use the solve_for_variables function
    // to create an appropriate "is_solved" tester and 
    // set the "state.is_solved" field at search time to
    // that function.
    Space.prototype.is_solved = function () {
        var i, v;
        for (i in this.vars) {
            v = this.vars[i];
            if (v.dom.length === 1) {
                if (v.dom[0][0] !== v.dom[0][1]) {
                    return false;
                } else {
                    // Singleton domain
                }
            } else {
                return false;
            }
        }

        return true;
    };

    // Returns an object whose field names are the fdvar names
    // and whose values are the solved values. The space *must*
    // be already in a solved state for this to work.
    Space.prototype.solution = function () {
        var result = {};
        var i, v, d;
        for (i in this.vars) {
            // Don't include the temporary variables in the "solution".
            // Temporary variables take the form of a numeric property
            // of the object, so we test for the key to be a number and
            // don't include those variables in the result.
            if (/^[0-9]+$/.test(i) === false) {
                v = this.vars[i];
                d = v.dom;
                result[i] = (d.length === 0 ? false : ((d.length > 1 || d[0][1] > d[0][0]) ? d : d[0][0]));
            }
        }
        return result;
    };

    // Utility to easily print out the state of variables in the space.
    Space.prototype.toString = function () {
        return JSON.stringify(this.solution());
    };

    // Injects the given proc into this space by calling
    // the proc with a single argument which is the current space.
    Space.prototype.inject = function (proc) {
        proc(this); // duh!
        return this;
    };

    Space.prototype.initprop = function (p) {
        p.last_step = -1;
        p.space = [this];
        var i, len;
        for (i = 0, len = p.allvars.length; i < len; ++i) {
            p.space.push(this.vars[p.allvars[i]]);
        }
        return p;
     };

    // Adds the new given propagator to this space and returns the space.
    Space.prototype.newprop = function (p) {
        this._propagators.push(this.initprop(p));
        return this;
    };

    // Returns a new unique name usable for a temporary fdvar
    // for more complex calculations. Every call will yield
    // a different name that is unique across all spaces.
    //
    // You can optionally specify a domain for the temporary
    // if you already know something about it.
    Space.prototype.temp = function (dom) {
        var t = ++(Space._temp_count);
        this.decl(t, dom);
        return t;
    };

    // Create N temporary FD variables and return their names
    // in an array.
    Space.prototype.temps = function (N, dom) {
        var i;
        var result = [];
        for (i = 0; i < N; ++i) {
            result.push(this.temp(dom));
        }
        return result;
    };

    // Create a "constant". We have no optimizing support for
    // constants at the moment and just treat it as a temp FDVar
    // whose domain is of size = 1.
    //
    // Fixing issue #1 - 'const' in the property position is not
    // accepted by the IE8 parser. It is likely to be rejected by
    // the closure compiler too. So I'm changing the name to 'konst' 
    // instead. I'll keep the old name 'const' for compatibility.
    Space.prototype.konst = function (val) {
        if (val < 0 || val > FD_SUP) {
            throw "FD.space.konst: Value out of valid range";
        }

        return this.temp([[val, val]]);
    };
    Space.prototype['const'] = Space.prototype.konst; // Keep old name for compatibility.

    function FDVar(dom, step) {
        this.dom = dom || [[0, FD_SUP]];
        this.step = step || 0;
    }

    FDVar.prototype = {
        is_undetermined: function () {
            return (this.dom.length > 1) || (this.dom[0][0] < this.dom[0][1]);
        },

        set_dom: function (d) {
            if (!domain_equal(this.dom, d)) { 
                this.dom = d; 
                this.step++; 
            } 
            return d; 
        },

        constrain: function (d) {
            return this.set_dom(domain_non_empty(domain_intersection(this.dom, d)));
        },

        size: function () {
            // TODO: Can be cached using the 'step' member which
            // keeps track of the number of times the domain was
            // changed.
            var i, N, s = 0;
            for (i = 0, N = this.dom.length; i < N; ++i) {
                s += this.dom[i][1] - this.dom[i][0] + 1;
            }
            return s;
        },

        min: function () {
            return this.dom[0][0];
        },

        max: function () {
            return this.dom[this.dom.length - 1][1];
        },

        // This "mid" function is quick to calculate and is a useful
        // compromise if you aren't really interested in the exact 
        // middle value, but something along the lines of "avoid the
        // extremes" as best as you can, as fast as you can.
        rough_mid: function () {
            var midDomIx = Math.floor(this.dom.length / 2);
            var midDom = this.dom[midDomIx];
            return Math.round((midDom[0] + midDom[1]) / 2);
        },

        // This is true "mid" function that returns the exact middle
        // value of the domain, but needs to run through the whole domain
        // to do it. Can be made more efficient, see TODO note below.
        mid: function () {
            var size = this.size();
            var midIx = Math.floor(size / 2);
            var domIx = 0;
            var dom = this.dom[domIx];

            // TODO: By right, we should do a binary search here
            // instead of a linear search. Yes, I'm lazy :P (Kumar)
            while (midIx > dom[1] - dom[0]) {
                midIx -= dom[1] - dom[0] + 1;
                domIx++;
                dom = this.dom[domIx];
            }

            return dom[0] + midIx; 
        }
    };

    // Once you create an fdvar in a space with the given
    // name, it is available for accessing as a direct member
    // of the space. Since this can cause a name clash, it is
    // recommended that you start the names of fdvars with an
    // upper case letter. Since all the declared member names
    // start with a lower case letter, a clash can certainly
    // be avoided if you stick to that rule.
    //
    // If the domain is not specified, it is taken to be [[0, FD_SUP]].
    //
    // Returns the space. All methods, unless otherwise noted,
    // will return the current space so that other methods
    // can be invoked in sequence.
    Space.prototype.decl = function (name_or_names, dom) {
        var i;

        if (name_or_names instanceof Object || name_or_names instanceof Array) {
            // Recursively declare all variables in the structure given.
            for (i in name_or_names) {
                this.decl(name_or_names[i], dom);
            }

            return this;
        }
        
        // A single variable is being declared.
        var name = name_or_names, fs = this.vars;
        var f = fs[name];
        if (f) { 
            // If it already exists, change the domain if necessary.
            if (dom) { f.set_dom(dom); }
            return this; 
        }

        fs[name] = new FDVar(dom);

        return this;
    };

    // Same function as var, but the domain is
    // that of a single number.
    Space.prototype.num = function(name, n) {
        return this.decl(name, [[n, n]]);
    };

    // Adds propagators which reify the given operator application
    // to the given boolean variable.
    //
    // `opname` is a string giving the name of the comparison
    // operator to reify. Currently, 'eq', 'neq', 'lt', 'lte', 'gt' and 'gte'
    // are supported.
    //
    // `argv` is an array of arguments accepted by the given 
    // comparison operator. Currently this *must* be an array of two
    // FD variable names.
    //
    // `boolname` is the name of the boolean variable to which to
    // reify the comparison operator. Note that this boolean
    // variable must already have been declared. If this argument
    // is omitted from the call, then the `reified` function can
    // be used in "functional style" and will return the name of
    // the reified boolean variable which you can pass to other
    // propagator creator functions.
    Space.prototype.reified = function (opname, argv, boolname) {
        var result, positive_propagator, negative_propagator;

        if (opname in Propagator.complementary_operator) {
            if (boolname) {
                this.vars[boolname].constrain([[0,1]]);
                result = this;
            } else {
                boolname = this.temp([[0,1]]);
                result = boolname;
            }

            console.log('GRAPH: ' + argv[0] + ' ' + opname + ' ' + argv[1] + ' :: ' + boolname);

            this[opname].apply(this, argv);
            positive_propagator = this._propagators.pop();

            this[Propagator.complementary_operator[opname]].apply(this, argv);
            negative_propagator = this._propagators.pop();

            var deps = argv.slice(0);
            deps.push(boolname);

            this.newprop({
                allvars: deps,
                depvars: deps,
                step: function () {
                    var S = this.space[0], v1 = this.space[1], v2 = this.space[2], b = this.space[3], bdom, snap, i, N, d, k, p, np;
                    var nextStep = v1.step + v2.step + b.step, f;
                    if (nextStep > this.last_step) {
                        // We need to make sure the `last_step` related changes
                        // are unique to this space, since p and np won't be
                        // borrowed into cloned spaces, since they aren't in 
                        // the `S._propagators` array.

                        if (false && this.solved) {
                            return 0;
                        }

                        if (!this.p) {                   
                            this.p = p = S.initprop({
                                allvars: positive_propagator.allvars, 
                                depvars: positive_propagator.depvars,
                                step: positive_propagator.step
                            });
                        } else {
                            p = this.p;
                        }

                        if (!this.np) {
                            this.np = np = S.initprop({
                                allvars: negative_propagator.allvars, 
                                depvars: negative_propagator.depvars,
                                step: negative_propagator.step
                             });
                        } else {
                            np = this.np;
                        }

                        do {
                            this.last_step = v1.step + v2.step + b.step;

                            bdom = b.dom[0];

                            if (bdom[0] === 1) {
                                p.step(); // may throw
                                this.solved = propagator_is_solved(S, p);
                            }

                            if (bdom[1] === 0) {
                                // The reified fdvar generates the negative condition.
                                np.step(); // may throw
                                this.solved = propagator_is_solved(S, np);
                            }

                            if (bdom[0] < bdom[1]) {
                                // The reified fdvar doesn't decide the condition, so
                                // we now need to check whether the conditions constrain
                                // the reified fdvar.
                                Propagator.save_vars(p);

                                try {
                                    p.step();
                                    Propagator.restore_vars(p);
                                } catch (e) {
                                    Propagator.restore_vars(p);
                                    b.constrain([[0, 0]]);
                                }

                                bdom = b.dom[0];
                            }

                            if (bdom[0] < bdom[1]) {
                                Propagator.save_vars(np);

                                try {
                                    np.step();
                                    Propagator.restore_vars(np);
                                } catch (e) {
                                    Propagator.restore_vars(np);
                                    b.constrain([[1, 1]]);
                                }
                            }
                        } while (v1.step + v2.step + b.step > this.last_step);

                        this.last_step = v1.step + v2.step + b.step;
                        return this.last_step - nextStep;
                    } else {
                        return 0;
                    }
                }
            });

            return result;
        } else {
            throw "FD.space.reified: Unsupported operator '" + opname + "'";
        }
    };

    // Domain equality propagator. Creates the propagator
    // in this space. The specified variables need not
    // exist at the time the propagator is created and
    // added, since the fdvars are all referenced by name.
    //
    // A convention for propagators is that the return
    // value of a propagator is number unless
    // the propagator has failed, in which case it throws
    // an exception 'fail'. The returned number indicates
    // the number of domains that were changed by this propagation
    // step. 
    //
    // The second optional argument indicates what you want the
    // propagator to do.
    Space.prototype.eq = function(v1name, v2name) {

        // If v2name is not specified, then we're operating in functional syntax
        // and the return value is expected to be v2name itself. This can happen
        // when, for example, scale uses a weight factor of 1.
        if (!v2name) {
            return v1name;
        }

        var p = {
            // Make available the list of fd variables that this
            // propagator affects. The space can check whether
            // a propagator is at its limit using this list.
            allvars: [v1name, v2name],
            depvars: [v1name, v2name],
            step: function () {
                var v1 = this.space[1], v2 = this.space[2];
                var nextStep = v1.step + v2.step;
                if (nextStep > this.last_step) {
                    var d = domain_non_empty(domain_intersection(v1.dom, v2.dom));
                    v1.set_dom(d);
                    v2.set_dom(d);
                    this.last_step = v1.step + v2.step;
                    return this.last_step - nextStep;
                } else {
                    return 0;
                }
            }
        };

        return this.newprop(p);
    };

    // Less than propagator. See general propagator nores
    // for fdeq which also apply to this one.
    Space.prototype.lt = function (v1name, v2name) {

        var p = {
            allvars: [v1name, v2name],
            depvars: [v1name, v2name],
            step: function () {
                var v1 = this.space[1], v2 = this.space[2];
                var nextStep = v1.step + v2.step;
                if (nextStep > this.last_step) {
                    var b1 = domain_bounds(v1.dom);
                    var b2 = domain_bounds(v2.dom);
                    this.last_step = nextStep;

                    if (b2[0] > b1[1]) {
                        // Condition already satisfied. No changes necessary.
                        // Change the step function to one that does almost no work.
//                        this.step = empty_propagation_step;
                        this.solved = true;                        
                        return 0;
                    }

                    var count = 0;

                    do {
                        this.last_step = v1.step + v2.step;
                        b1 = domain_bounds(v1.dom);
                        b2 = domain_bounds(v2.dom);

                        if (b2[1] - 1 < b1[1]) {
                            // Need to change domain of v1.
                            v1.set_dom(domain_non_empty(domain_intersection(v1.dom, [[b1[0], b2[1] - 1]])));
                        }

                        if (b1[0] + 1 > b2[0]) {
                            // Need to change domain of v2.
                            v2.set_dom(domain_non_empty(domain_intersection(v2.dom, [[b1[0] + 1, b2[1]]])));
                        }
                    } while (v1.step + v2.step > this.last_step);

                    return (this.last_step = v1.step + v2.step) - nextStep;
                } else {
                    return 0;
                }
            }
        };

        return this.newprop(p);
    };

    // Greater than propagator.
    Space.prototype.gt = function (v1name, v2name) {
        return this.lt(v2name, v1name);
    };

    // Less than or equal to propagator.
    Space.prototype.lte = function (v1name, v2name) {

        var p = {
            allvars: [v1name, v2name],
            depvars: [v1name, v2name],
            step: function () {
                var v1 = this.space[1], v2 = this.space[2];
                var nextStep = v1.step + v2.step;
                if (nextStep > this.last_step) {
                    var b1 = domain_bounds(v1.dom);
                    var b2 = domain_bounds(v2.dom);
                    this.last_step = nextStep;

                    if (b2[0] >= b1[1]) {
                        // Condition already satisfied. No changes necessary.
                        // Change the step function to one that does almost no work.
//                        this.step = empty_propagation_step;
                        this.solved = true;                        
                        return 0;
                    }

                    var count = 0;

                    do {
                        this.last_step = v1.step + v2.step;
                        b1 = domain_bounds(v1.dom);
                        b2 = domain_bounds(v2.dom);

                        if (b2[1] < b1[1]) {
                            // Need to change domain of v1.
                            v1.set_dom(domain_non_empty(domain_intersection(v1.dom, [[b1[0], b2[1]]])));
                        }

                        if (b1[0] > b2[0]) {
                            // Need to change domain of v2.
                            v2.set_dom(domain_non_empty(domain_intersection(v2.dom, [[b1[0], b2[1]]])));
                        }
                    } while (v1.step + v2.step > this.last_step)

                    return (this.last_step = v1.step + v2.step) - nextStep;
                } else {
                    return 0;
                }
            }
        };

        return this.newprop(p);
    };

    // Greater than or equal to.
    Space.prototype.gte = function (v1name, v2name) {
        return this.lte(v2name, v1name);
    };

    // Ensures that the two variables take on different values.
    Space.prototype.neq = function (v1name, v2name) {

        var p = {
            allvars: [v1name, v2name],
            depvars: [v1name, v2name],
            step: function () {
                var v1 = this.space[1], v2 = this.space[2];
                var nextStep = v1.step + v2.step;
                if (nextStep > this.last_step) {
                    var b1 = domain_bounds(v1.dom);
                    var b2 = domain_bounds(v2.dom);
                    this.last_step = nextStep;

                    if (b2[0] > b1[1] || b1[1] < b2[0]) {
                        // Condition already satisfied. No changes necessary.
                        // Change the step function to one that does almost no work.
//                        this.step = empty_propagation_step;
                        this.solved = true;                        
                        return 0;
                    }

                    var v12 = domain_intersection(v1.dom, v2.dom);
                    if (v12.length === 0) {
                        // Condition already satisfied.
                        // Change the step function to one that does almost no work.
//                        this.step = empty_propagation_step;
                        this.solved = true;                        
                        return 0;
                    }

                    do {
                        this.last_step = v1.step + v2.step;
                        b1 = domain_bounds(v1.dom);
                        b2 = domain_bounds(v2.dom);

                        if (b1[0] === b1[1]) {
                            v2.set_dom(domain_non_empty(domain_intersection(v2.dom, domain_complement([b1]))));
                        }

                        if (b2[0] === b2[1]) {
                            v1.set_dom(domain_non_empty(domain_intersection(v1.dom, domain_complement([b2]))));
                        }
                    } while (v1.step + v2.step > this.last_step);

                    this.last_step = v1.step + v2.step;
                    return this.last_step - nextStep;
                } else {
                    return 0;
                }
            }
        };

        return this.newprop(p);        
    };

    // Takes an arbitrary number of FD variables and adds propagators that
    // ensure that they are pairwise distinct.
    Space.prototype.distinct = function (vars) {
        var i, j, len;
        for (i = 0, len = vars.length; i < len; ++i) {
            for (j = 0; j < i; ++j) {
                this.neq(vars[i], vars[j]);
            }
        }
        return this;
    };


    function ring(plusop, minusop, v1name, v2name, sumname) {
        var retval = this;

        // If sumname is not specified, we need to create a temp
        // for the result and return the name of that temp variable.
        if (!sumname) {
            sumname = this.temp();
            retval = sumname;
        }

        console.log('GRAPH: ' + v1name + ' + ' + v2name  + ' = ' + sumname);

        this.newprop({
            allvars: [v1name, v2name, sumname],
            depvars: [v1name, v2name],
            step: function () {
                var v1 = this.space[1], v2 = this.space[2], sum = this.space[3];
                var nextStep = v1.step + v2.step + sum.step;

                if (nextStep > this.last_step) {
                    sum.set_dom(domain_non_empty(domain_intersection(plusop(v1.dom, v2.dom), sum.dom)));
                    this.last_step = sum.step + v1.step + v2.step;
                }

                return this.last_step - nextStep;
            }
        });

        this.newprop({
            allvars: [v1name, v2name, sumname],
            depvars: [v2name, sumname],
            step: function () {
                var v1 = this.space[1], v2 = this.space[2], sum = this.space[3];
                var nextStep = v1.step + v2.step + sum.step;

                if (nextStep > this.last_step) {
                    v1.set_dom(domain_non_empty(domain_intersection(minusop(sum.dom, v2.dom), v1.dom)));
                    this.last_step = sum.step + v1.step + v2.step;
                }

                return this.last_step - nextStep;
            }
        });

        this.newprop({
            allvars: [v1name, v2name, sumname],
            depvars: [v1name, sumname],
            step: function () {
                var v1 = this.space[1], v2 = this.space[2], sum = this.space[3];
                var nextStep = v1.step + v2.step + sum.step;

                if (nextStep > this.last_step) {
                    v2.set_dom(domain_non_empty(domain_intersection(minusop(sum.dom, v1.dom), v2.dom)));
                    this.last_step = sum.step + v1.step + v2.step;
                }

                return this.last_step - nextStep;
            }
        });

        return retval;
    };

    // Bidirectional addition propagator.
    Space.prototype.plus = function (v1name, v2name, sumname) {
        return ring.call(this, dom_plus, dom_minus, v1name, v2name, sumname);
    };

    // Bidirectional multiplication propagator.
    Space.prototype.times = function (v1name, v2name, prodname) {
        return ring.call(this, dom_times, dom_divby, v1name, v2name, prodname);
    };

    // factor = constant number (not an fdvar)
    // vname is an fdvar name
    // prodname is an fdvar name.
    //
    // factor * v = prod
    Space.prototype.scale = function (factor, vname, prodname) {
        if (factor === 1) {
            return this.eq(vname, prodname);
        } else if (factor === 0) {
            return this.eq(this.temp([[0, 0]]), prodname);
        } else if (factor < 0) {
            throw "scale: negative factors not supported.";
        }

        var retval = this;
        if (!prodname) {
            prodname = this.temp();
            retval = prodname;
        }

        this.newprop({
            allvars: [vname, prodname],
            depvars: [vname],
            step: function () {
                var v = this.space[1], prod = this.space[2];
                var nextStep = v.step + prod.step;
                if (nextStep > this.last_step) {
                    var bd = domain_bounds(v.dom);
                    var kd, l, r;

                    // We multiply only the interval bounds.
                    kd = v.dom.map(function (i) { return [Math.min(FD_SUP, i[0] * factor), Math.min(FD_SUP, i[1] * factor)]; });

                    prod.set_dom(domain_non_empty(domain_intersection(kd, prod.dom)));

                    return (this.last_step = v.step + prod.step) - nextStep;
                } else {
                    return 0;
                }
             }
        });

        this.newprop({
            allvars: [vname, prodname],
            depvars: [prodname],
            step: function () {
                var v = this.space[1], prod = this.space[2];
                var nextStep = v.step + prod.step;
                if (nextStep > this.last_step) {
                    var dbyk, l, r;

                    dbyk = simplify_domain(prod.dom.map(function (i) {
                        l = i[0] / factor;
                        r = i[1] / factor;
                        return [l - l % 1, r - r % 1];
                    }));

                    v.set_dom(domain_non_empty(domain_intersection(dbyk, v.dom)));

                    return (this.last_step = v.step + prod.step) - nextStep;
                } else {
                    return 0;
                }
            }
        });
        
        return retval;
    };

    // TODO: Can be made more efficient.
    Space.prototype.times_plus = function (k1, v1name, k2, v2name, resultname) {
        return this.plus(this.scale(k1, v1name), this.scale(k2, v2name), resultname);
    };

    // Sum of N fdvars = resultFDVar
    // Creates as many temporaries as necessary.
    Space.prototype.sum = function (vars, resultName) {
        var n, N, t1, t2;
        var retval = this;
        if (!resultName) {
            resultName = this.temp();
            retval = resultName;
        }

        switch (vars.length) {
            case 0: throw "Space.sum: Nothing to sum!";
            case 1: this.eq(vars[0], resultName); return retval;
            case 2: this.plus(vars[0], vars[1], resultName); return retval;
            default:
                n = vars.length >> 1;
                t2 = this.temp();
                this.sum(vars.slice(n), t2);
                if (n > 1) {
                    t1 = this.temp();
                    this.sum(vars.slice(0, n), t1);
                } else {
                    t1 = vars[0];
                }
                this.plus(t1, t2, resultName);
                return retval;
        }
    };

    // Product of N fdvars = resultFDvar.
    // Create as many temporaries as necessary.
    Space.prototype.product = function (vars, resultName) {
        var n, t1, t2;
        var retval = this;
        if (!resultName) {
            resultName = this.temp();
            retval = resultName;
        }

        switch (vars.length) {
            case 0: return retval;
            case 1: this.eq(vars[0], resultName); return retval;
            case 2: this.times(vars[0], vars[1], resultName); return retval;
            default:
                n = vars.length >> 1;
                t2 = this.temp();
                this.product(vars.slice(n), t2);
                if (n > 1) {
                    t1 = this.temp();
                    this.product(vars.slice(0, n), t1);
                } else {
                    t1 = vars[0];
                }
                this.times(t1, t2, resultName);
                return retval;
        }
    };

    // Weighted sum of fdvars where the weights are constants.
    Space.prototype.wsum = function (kweights, vars, resultName) {
        var temps = [];
        var i, len, t;
        for (i = 0, len = vars.length; i < len; ++i) {
            t = this.temp();
            this.scale(kweights[i], vars[i], t);
            temps.push(t);
        }
        return this.sum(temps, resultName);
    }

    // Closes all the gaps between the intervals according to
    // the given gap value. All gaps less than this gap are closed.
    function dom_close_gaps(d, gap) {
        if (d.length === 0) { return d; }

        var result = [];
        var i, len, prev, next;
        result.push(prev = [d[0][0], d[0][1]]);
        for (i = 1, len = d.length; i < len; ++i) {
            next = [d[i][0], d[i][1]];
            if (next[0] - prev[1] < gap) {
                prev[1] = next[1];
            } else {
                result.push(prev = next);
            }
        }

        return result;
    }

    function dom_smallest_interval_width(d) {
        return Math.min.apply(null, d.map(function (i) { return i[1] - i[0] + 1; }));
    }

    function dom_largest_interval_width(d) {
        return Math.max.apply(null, d.map(function (i) { return i[1] - i[0] + 1; }));
    }

    // The idea behind this function - which is primarily
    // intended for dom_plus and dom_minus and porbably applies
    // to nothing else - is that when adding two intervals,
    // both intervals expand by the other's amount. This means
    // that when given two segmented domains, each continuous
    // subdomain expands by at least the interval of the smallest
    // subdomain of the other segmented domain. When such an expansion
    // occurs, any gaps between subdomains that are <= the smallest
    // subdomain's interval width get filled up, which we can exploit 
    // to reduce the number of segments in a domain. Reducing the
    // number of domain segments helps reduce the N^2 complexity of
    // the subsequent domain consistent interval addition method.
    function dom_close_gaps2(d1, d2) {
        var d, change;
        do {
            change = 0;
            d = dom_close_gaps(d1, dom_smallest_interval_width(d2));
            change += d1.length - d.length;
            d1 = d;
            d = dom_close_gaps(d2, dom_smallest_interval_width(d1));
            change += d2.length - d.length;
            d2 = d;
        } while (change > 0);

        return [d1, d2];
    }

    function dom_plus(d1, d2) {
        var d, i, j, len1, len2, i1, i2, p = [];
        var change;

        // Simplify the domains by closing gaps since when we add
        // the domains, the gaps will close according to the
        // smallest interval width in the other domain.
        d = dom_close_gaps2(d1, d2);
        d1 = d[0];
        d2 = d[1];

        for (i = 0, len1 = d1.length, len2 = d2.length; i < len1; ++i) {
            i1 = d1[i];
            for (j = 0; j < len2; ++j) {
                i2 = d2[j];
                p.push([Math.min(FD_SUP, i1[0] + i2[0]), Math.min(FD_SUP, i1[1] + i2[1])]);
            }
        }

        return simplify_domain(p);
    }

    // Note that this one isn't domain consistent.
    function dom_times(d1, d2) {
        var i, j, len1, len2, i1, i2, p = [];
        for (i = 0, len1 = d1.length, len2 = d2.length; i < len1; ++i) {
            i1 = d1[i];
            for (j = 0; j < len2; ++j) {
                i2 = d2[j];
                p.push([Math.min(FD_SUP, i1[0] * i2[0]), Math.min(FD_SUP, i1[1] * i2[1])]);
            }
        }

        return simplify_domain(p);
    }

    function dom_minus(d1, d2) {
        var d, i, j, len1, len2, i1, i2, p = [], lo, hi;

        // Simplify the domains by closing gaps since when we add
        // the domains, the gaps will close according to the
        // smallest interval width in the other domain.
        d = dom_close_gaps2(d1, d2);
        d1 = d[0];
        d2 = d[1];

        for (i = 0, len1 = d1.length, len2 = d2.length; i < len1; ++i) {
            i1 = d1[i];
            for (j = 0; j < len2; ++j) {
                i2 = d2[j];
                lo = i1[0] - i2[1];
                hi = i1[1] - i2[0];
                if (hi >= 0) {
                    p.push([(lo < 0 ? 0 : lo), hi]);
                }
            }
        }

        return simplify_domain(p);
    }

    // Note that this isn't domain consistent.
    function dom_divby(d1, d2) {
        var i, j, len1, len2, i1, i2, p = [], lo, hi;
        for (i = 0, len1 = d1.length, len2 = d2.length; i < len1; ++i) {
            i1 = d1[i];
            for (j = 0; j < len2; ++j) {
                i2 = d2[j];
                if (i2[1] > 0) {
                    lo = i1[0] / i2[1];
                    hi = (i2[0] > 0 ? (i1[1] / i2[0]) : FD_SUP);
                    if (hi >= 0) {
                        p.push([(lo < 0 ? 0 : lo), hi]);
                    }
                }
            }
        }

        return simplify_domain(p);
    }

    /////////////////////////////////////////////////////////////////
    // Modular distribution strategies.
    var Distribute = {};

    // The generic distributor.
    Distribute.generic = function (S, varnames, spec) {
       
        function select_by_order(S, vars, orderingfn) {
            if (vars.length > 0) {
                if (vars.length === 1) {
                    return vars[0];
                }

                var i, N, first = 0;
                for (i = 1, N = vars.length; i < N; ++i) {
                    if (!orderingfn(S, vars[first], vars[i])) {
                        first = i;
                    }
                }

                return vars[first];
            } else {
                return null;
            }
        }

        var branch_sequence = {};
        var filterfn = (typeof(spec.filter) === 'string') ? Distribute.generic.filters[spec.filter] : spec.filter;
        var orderingfn = (typeof(spec.ordering) === 'string') ? Distribute.generic.orderings[spec.ordering] : spec.ordering;
        var valuefn = (typeof(spec.value) === 'string') ? Distribute.generic.values[spec.value] : spec.value;

        if (!filterfn || !orderingfn || !valuefn) {
            throw 'FD.distribute.generic: Invalid spec';
        }

        // The role of the branch() function is to produce a function (S, n)
        // that will return S with the choice point n committed. The function's
        // 'numChoices' property will tell you how many choices are available.
        branch_sequence.branch = function (S) {
            var vars, v, doms, Sc;

            vars = filterfn(S, varnames);
            if (vars.length > 0) {
                v = select_by_order(S, vars, orderingfn);

                return v ? valuefn(v) : null;
            } else {
                return null;
            }
        };

        S.brancher.enqueue(branch_sequence);
        return S;
    };

    Distribute.generic.filters = {
        undet: function (S, varnames) {
            var i, N, vs = [];
            for (i = 0, N = varnames.length; i < N; ++i) {
                if (S.vars[varnames[i]].is_undetermined()) {
                    vs.push(varnames[i]);
                }
            }

            return vs;
        }
    };

    Distribute.generic.orderings = {
        naive: function (S, v1, v2) {
            return true;
        },

        size: function (S, v1, v2) {
            return S.vars[v1].size() < S.vars[v2].size();
        },

        min: function (S, v1, v2) {
            return S.vars[v1].min() < S.vars[v2].min();
        },

        max: function (S, v1, v2) {
            return S.vars[v1].max() > S.vars[v2].max();
        }
    };

    // The interface contract for "values" functions is that
    // they take a variable name and return a function that will
    // impose a sequence of choices on the variable into a given
    // space. The returned function (S, n) will commit the given
    // space S to a choice for the originally specified variable.
    // The returned function's "numChoices" property tells you
    // how many choices are available, and the choices are numbered
    // from 0 to numChoices-1.
    //
    // Note that this change of interface has resulted in a noticeable
    // performance degradation. My guess is that the degradation is due
    // to the computations outside the switch blocks having to execute
    // for every choice, whereas in the earlier implementation there
    // were only executed once per space.
    Distribute.generic.values = {

        // Picks the smallest value in the domain first.
        min: function (v) {
            function options(S, n) {
                var vS = S.vars[v];
                var d = vS.min();
                switch (n) {
                    case 0: 
                        vS.constrain([[d, d]]);
                        return S;
                    case 1: 
                        vS.constrain([[d+1, vS.max()]]);
                        return S;
                    default: 
                        throw new Error("Invalid choice");
                }
            }

            options.numChoices = 2;
            return options;
        },

        // Picks the largest value in the domain first.
        max: function (v) {
            function options(S, n) {
                var vS = S.vars[v];
                var d = vS.max();
                switch (n) {
                    case 0:
                        vS.constrain([[d, d]]);
                        return S;
                    case 1:
                        vS.constrain([[vS.min(), d-1]]);
                        return S;
                    default:
                        throw new Error("Invalid choice");
                }
            }

            options.numChoices = 2;
            return options;
        },

        // Picks the middle value in the domain first.
        mid: function (v) {
            function options(S, n) {
                var fv = S.vars[v];
                var d = fv.mid();
                if (n === 0) {
                    fv.constrain([[d, d]]);
                    return S;
                } else if (n === 1) {
                    if (d > fv.min()) {
                        fv.constrain([[fv.min(), d-1], [d+1, fv.max()]]);
                        return S;
                    } else {
                        fv.constrain([[d+1, fv.max()]]);
                        return S;
                    }
                } else {
                    throw new Error("Invalid choice");
                }
            }

            options.numChoices = 2;
            return options;
        },

        // splits the domain roughly down the middle, trying the
        // lower values first.
        splitMin: function (v) {
            function options(S, n) {
                var vS = S.vars[v];
                var d = vS.dom;
                var m = (d[0][0] + d[d.length - 1][1]) >> 1;
                switch (n) {
                    case 0:
                        vS.constrain([[d[0][0], m]]);
                        return S;
                    case 1: 
                        vS.constrain([[m+1, d[d.length - 1][1]]]);
                        return S;
                    default:
                        throw new Error("Invalid choice");
                }
            }

            options.numChoices = 2;
            return options;
        },

        // splits the domain roughly down the middle, trying the
        // higher values first.
        splitMax: function (v) {
            function options(S, n) {
                var vS = S.vars[v];
                var d = vS.dom;
                var m = (d[0][0] + d[d.length - 1][1]) >> 1;
                switch (n) {
                    case 0:
                        vS.constrain([[m+1, d[d.length - 1][1]]]);
                        return S;
                    case 1:
                        vS.constrain([[d[0][0], m]]);
                        return S;
                    default:
                        throw new Error("Invalid choice");
                }
            }

            options.numChoices = 2;
            return options;
        }
    };

    // The native distribution strategy simply steps through all
    // undetermined variables.
    Distribute.naive = (function () {
        var spec = {
            filter: 'undet',
            ordering: 'naive',
            value: 'min'
        };

        return function (S, varnames) {
            return Distribute.generic(S, varnames, spec);
        };
    }());

    // The "fail first" strategy branches on the variable with the
    // smallest domain size.
    Distribute.fail_first = (function () {
        var spec = {
            filter: 'undet',
            ordering: 'size',
            value: 'min'
        };

        return function (S, varnames) {
            return Distribute.generic(S, varnames, spec);
        };
    }());

    // The "domain splitting" strategy where each domain is roughly
    // halved in each step. The 'varname' argument can be either a
    // single fdvar name or an array of names or an object whose
    // values are fdvar names.
    Distribute.split = (function () {
        var spec = {
            filter: 'undet',
            ordering: 'size',
            value: 'splitMin'
        };

        return function (S, varnames) {
            return Distribute.generic(S, varnames, spec);
        };
    }());
            
    // Search using the branchers.
    var Search = {};

    // A "class function" for making "is_solved" testers
    // for use during search.
    Search.solve_for_variables = function (varnames) {
        if (varnames) {
            return function (S) {
                var i, N, v;
                for (i = 0, N = varnames.length; i < N; ++i) {
                    v = S.vars[varnames[i]];
                    if (v.dom.length === 1) {
                        if (v.dom[0][0] !== v.dom[0][1]) {
                            return false;
                        } else {
                            // Singleton domain
                        }
                    } else {
                        return false;
                    }
                }
                return true;
            };
        } else {
            return function (S) { 
                return S.is_solved(); 
            };
        }
    };

    Search.solve_for_propagators = function (S) {
        var i, N, p;
        for (i = 0, N = S._propagators.length; i < N; ++i) {
            if (!propagator_is_solved(S, S._propagators[i])) {
                return false;
            }
        }
        return true;
    };

    // A simple mechanism for branching down a search tree where the
    // choice points function and info about the number of choices
    // are both stored in the space itself. This doesn't have to be
    // the case, however, and you can roll your own strategy and
    // pass it in the "state.next_choice" field.
    //
    // This implementation stores information that is local to
    // a space in the space itself. That doesn't have to be the
    // case and the whole search state is passed in which you
    // can make use of for tracking purposes. For example, you can 
    // have a stack of choice functions that you can use to recompute
    // a space at any depth by starting from the root and applying
    // the options in sequence to a clone of the root space. 
    //
    // The implementation below suffices for the depth_first and
    // branch_and_bound search strategies.
    function next_choice(space, state) {
        if (!space.commit) {
            // Note that the branch call is made only once, irrespective
            // of how many children this space might generate. The branch
            // call now returns a choice function that constrains a chosen
            // variable to a domain indexed by a choice number.
            space.commit = space.brancher.branch();
            if (space.commit) {
                space.commit.nextChoice = 0;
            }
        }

        if (space.commit && space.commit.nextChoice < space.commit.numChoices) {
            // Clone the given space and commit it to the next available choice.
            // Returned the commited cloned space.
            return space.commit(space.clone(), space.commit.nextChoice++);
        } else {
            return null;
        }
    }

    // Depth first search.
    // state.space must be the starting space. The object is used to store and 
    // track continuation information from that point onwards.
    //
    // On return, state.status contains either 'solved' or 'end' to indicate
    // the status of the returned solution. Also state.more will be true if
    // the search can continue and there may be more solutions.
    Search.depth_first = function (state) {
        var space = state.space;
        var stack = state.stack;
        var brancher, next_space, choose_next_space;

        // If no stack argument, then search begins with this space.
        if (!stack || stack.length === 0) {
            stack = state.stack = [space];
        }

        if (!state.is_solved) {
            // Set the default "solved" condition to be "all variables".
            state.is_solved = Search.solve_for_variables();
        }

        if (!state.next_choice) {
            // Set the default branch generator to the next_choice
            // function, which is a simple implementation of generating
            // branches from index 0 to N-1.
            state.next_choice = next_choice;
        }

        choose_next_space = state.next_choice;

        while (stack.length > 0) {
            space = stack[stack.length - 1];

            try {
                // Wait for stability. Could throw a 'fail', in which case
                // this becomes a failed space.
                space.propagate();

                if (state.is_solved(space)) {
                    space.succeeded_children++;
                    space.done();
                    stack.pop();
                    state.status = 'solved';
                    state.space = space;
                    state.more = stack.length > 0;
                    return state;
                }

                // Now this space is neither solved nor failed,
                // therefore it is stable. (WARNING: Is this correct?)

                // Call up the next brancher and fork the space
                // according to what it says.
                next_space = choose_next_space(space, state);
                if (next_space) {
                    // Push on to the stack and explore further.
                    stack.push(next_space);
                } else {
                    // Finished exploring branches of this space. Continue with the previous spaces.
                    // This is a stable space, but isn't a solution. Neither is it a failed space.
                    space.stable_children++;
                    space.done();
                    stack.pop();
                    state.more = stack.length > 0;
                }
            } catch (e) {
                // Some propagators failed so this is now a failed space and we need
                // to pop the stack and continue from above. This is a failed space.
                space.failed = true;
                space.done();
                stack.pop();
            }
        }

        // Failed space and no more options to explore.
        state.status = 'end';
        state.more = false;
        return state;
    };

    // Branch and bound search
    // WARNING: Untested!
    // TODO: Test this function and once the tests pass, remove the above warning.
    //
    // Finds the "best" solution according to the given ordering function.
    // The `state` parameter is similar to the `depth_first` search function.
    // It is expected to be an object such that `state.space` gives the space
    // from which to search for the best solution.
    //
    // The `state` is also what is returned by `branch_and_bound` and `state.space`
    // will be the space with the best solution found during the search. When a
    // solution exists, `state.status` will be the string "solved".
    //
    // The `ordering` argument is expected to be a function of the form
    //       function (space, a_solution) { ... }
    // where the `space` argument is the space into which the ordering function
    // should inject the new constraints for the ordering, and `a_solution` is
    // an object whose keys are root finite domain variable names and whose
    // values are the solved values of those variables. The return value of
    // the ordering function is irrelevant.
    //
    // There are two ways to use the branch_and_bound function -
    //    1. In one shot mode where a single call will give you the best
    //       solution that it can find, if a solution exists at all.
    //
    //    2. In "single step" mode, indicated by setting `state.single_step` to `true`.
    //       In this mode, the function will return whenever it finds a solved space
    //       and `state.more` will indicate whether there may be any more solutions
    //       to look at. In this mode, every call will result in a solution that is
    //       "better" than the one found before it, due to the `ordering` function.
    //
    //       Note that if `state.more` is `false`, then definitely there are no
    //       more solutions to look at, but if it is `true`, there *may* be more
    //       solutions to look at. If a subsequent search turns up empty, it is
    //       indicated by `state.status` being set to the string "end".
    //
    Search.branch_and_bound = function (state, ordering) {
        var space = state.space;
        var stack = state.stack;
        var brancher, next_space, choose_next_space;
        var bestSolution = state.best;

        if (state.error) {
            // If a search tree state with an error is passed in,
            // we throw up immediately.
            throw state;
        }

        // If no stack argument, then search begins with this space.
        if (!stack || stack.length === 0) {
            stack = state.stack = [space];
        }

        if (!state.is_solved) {
            // Set the default "solved" condition to be "all variables".
            state.is_solved = Search.solve_for_variables();
        }

        if (!state.next_choice) {
            // Set the default branch generator to the next_choice
            // function, which is a simple implementation of generating
            // branches from index 0 to N-1.
            state.next_choice = next_choice;
        }

        choose_next_space = state.next_choice;

        while (stack.length > 0) {
            space = stack[stack.length - 1];

            try {
                // Wait for stability. Could throw a 'fail', in which case
                // this becomes a failed space.
                space.propagate();

                if (state.is_solved(space)) {
                    space.succeeded_children++;
                    space.done();
                    stack.pop();
                    state.status = 'solved';
                    state.space = space;
                    state.more = stack.length > 0;

                    // This space is now our "current best solution"
                    state.best = bestSolution = space;

                    // We now try to find something better based on the given
                    // ordering.
                    if (state.more) {
                        next_space = choose_next_space(stack[stack.length - 1], state);
                        while (!next_space && stack.length > 0) {
                            stack[stack.length - 1].done();
                            stack.pop();
                            if (stack.length > 0) {
                                next_space = choose_next_space(stack[stack.length - 1], state);
                            } else {
                                break;
                            }
                        }
                        if (next_space) {
                            // Constrain the search to be better than our current best solution.
                            ordering(next_space, bestSolution.solution());
                            state.needs_constraining = false;
                            stack.push(next_space);

                            // Continue the search. If we've been asked to
                            // single step, then just return the current state.
                            // the stack is already prepared so that the next call
                            // will initiate a search for a solution that is better
                            // than the one in state.space.
                            if (state.single_step) {
                                return state;
                            } else {
                                continue;
                            }
                        } else {
                            // No more spaces to explore. We've already found
                            // the best solution that we can find in this tree.
                            state.more = false;
                        }
                    } 

                    // We have no more branches to explore.
                    // Return the best solution found so far.
                    return state;
                }

                // Now this space is neither solved nor failed,
                // therefore it is stable. (WARNING: Is this correct?)

                // Call up the next brancher and fork the space
                // according to what it says.
                next_space = choose_next_space(space, state);
                if (next_space) {
                    // Push on to the stack and explore further.
                    if (state.needs_constraining && bestSolution) {
                        ordering(next_space, bestSolution.solution());
                    }
                    state.needs_constraining = false;
                    stack.push(next_space);
                } else {
                    // Finished exploring branches of this space. Continue with the previous spaces.
                    // This is a stable space, but isn't a solution. Neither is it a failed space.
                    //
                    // TODO: Ideally, this condition should never occur and if it does, it is 
                    // likely to be an error in the problem specification. Maybe I should
                    // throw up here?
                    space.stable_children++;
                    space.done();
                    stack.pop();
                    state.more = stack.length > 0;
                    state.needs_constraining = true;
                }
            } catch (e) {
                // Some propagators failed so this is now a failed space and we need
                // to pop the stack and continue from above. This is a failed space.
                space.failed = true;
                space.done();
                stack.pop();
                state.more = stack.length > 0;
                state.needs_constraining = true;
            }
        }

        // Failed space and no more options to explore.
        state.status = (bestSolution ? 'solved' : 'end');
        state.more = false;

        // Note that state.space already contains the last - i.e. the "best" solution,
        // If the original space passed to branch_and_bound actually has no solution,
        // then state.space.failed will be true.
        return state;
    };


    exports.SUP = FD_SUP;
    exports.INF = 0;
    exports.space = Space;
    exports.distribute = Distribute;
    exports.search = Search;

    return exports;
})({}, Math);

try {
    module.exports = FD;
} catch (e) {
    // Not in node.js. Likely loaded as FD in a browser.
}
