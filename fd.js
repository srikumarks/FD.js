// Copyright (c) 2011, Srikumar K. S. (srikumarks@gmail.com)
// All rights reserved.
//
// Redistribution license: BSD (http://www.opensource.org/licenses/bsd-license.php)
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
        this.queue = (brancher ? brancher.queue : []);
        this.next_brancher = (brancher ? (brancher.next_brancher + 1) : 0);
    }

    Brancher.prototype = {
        branch: function () {
            // Note that the "next brancher" field will be
            // taken from the deepest space's brancher object
            // due to access via 'this'. However, the queue
            // is an array whose contents are common to all 
            // branchers part of the same tree.
            var b = this.queue[this.next_brancher];
            return b ? b.branch.call(this, this.space) : null;
        },

        enqueue: function (b) {
            // Note that the queue is common to all spaces
            // starting from the parent space, but the
            // 'next_brancher' index is local to the brancher
            // belonging to each space.
            this.queue.push(b);
            return this;
        }
    };

    // A propagator is solved if all the depvars it affects and
    // depends on have domains of size = 1.
    function propagator_is_solved(S, p) {
        var i, len, b;
        for (i = 0, len = p.allvars.length; i < len; ++i) {
            b = S.vars[p.allvars[i]].dom;
            if (b.length > 0 || b[0][1] > b[0][0]) {
                return false;
            }
        }
        return true;
    }

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

        return this;
    }

    // Duplicates the functionality of new Space(S) for readability.
    Space.prototype.clone = function () {
        return new Space(this);
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
        return totalCount;
    };

    // Returns true if this space is solved - i.e. when
    // all the fdvars in the space have a singleton domain.
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

    // Injects the given proc into this space by calling
    // the proc with a single argument which is the current space.
    Space.prototype.inject = function (proc) {
        proc(this); // duh!
        return this;
    };

    // Adds the new given propagator to this space and returns the space.
    Space.prototype.newprop = function (p) {
        p.last_step = -1;
        p.space = [this];
        var i, len;
        for (i = 0, len = p.allvars.length; i < len; ++i) {
            p.space.push(this.vars[p.allvars[i]]);
        }
        this._propagators.push(p);
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

    function FDVar(dom, step) {
        this.dom = dom || [[0, FD_SUP]];
        this.step = step || 0;
    }

    FDVar.prototype = {
        set_dom: function (d) {
            if (!domain_equal(this.dom, d)) { 
                this.dom = d; 
                this.step++; 
            } 
            return d; 
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
                        return 0;
                    }

                    var count = 0;

                    if (b2[1] - 1 < b1[1]) {
                        // Need to change domain of v1.
                        v1.set_dom(domain_non_empty(domain_intersection(v1.dom, [[b1[0], b2[1] - 1]])));
                    }

                    if (b1[0] + 1 > b2[0]) {
                        // Need to change domain of v2.
                        v2.set_dom(domain_non_empty(domain_intersection(v2.dom, [[b1[0] + 1, b2[1]]])));
                    }

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
                        return 0;
                    }

                    var count = 0;

                    if (b2[1] < b1[1]) {
                        // Need to change domain of v1.
                        v1.set_dom(domain_non_empty(domain_intersection(v1.dom, [[b1[0], b2[1]]])));
                    }

                    if (b1[0] > b2[0]) {
                        // Need to change domain of v2.
                        v2.set_dom(domain_non_empty(domain_intersection(v2.dom, [[b1[0], b2[1]]])));
                    }

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
                        return 0;
                    }

                    var v12 = domain_intersection(v1.dom, v2.dom);
                    if (v12.length === 0) {
                        // Condition already satisfied.
                        return 0;
                    }

                    if (b1[0] === b1[1]) {
                        v2.set_dom(domain_non_empty(domain_intersection(v2.dom, domain_complement([b1]))));
                    }

                    if (b2[0] === b2[1]) {
                        v1.set_dom(domain_non_empty(domain_intersection(v1.dom, domain_complement([b2]))));
                    }

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

    // Distribution strategies.
    var Distribute = {
        naive: function (S, varname) {
            var i;

            // Handle aggregates in place of varname as well.
            if (varname instanceof Array || varname instanceof Object) {
                for (i in varname) {
                    this.naive(S, varname[i]);
                }
                return S;
            }

            var v = S.vars[varname];
            var dom = v.dom;

            var branch_sequence = (function () {
                return {
                    branch: function (S) {
                        var state = S.__branch_state || (S.__branch_state = {i: 0, val: dom[0][0]});
                        if (state.val > dom[state.i][1]) {
                            state.i++;
                            if (state.i >= dom.length) {
                                // No more branch possibilities.
                                return null;
                            }
                            state.val = dom[state.i][0];
                        }

                        var Sc = S.clone();
                        var vc = Sc.vars[varname];
                        vc.set_dom([[state.val, state.val]]);
                        state.val++;
                        return Sc;
                    }
                };
            })();

            S.brancher.enqueue(branch_sequence);
            return S;
        },

        fail_first: function (S, varnames) {

            function var_with_smallest_domain() {
                var ds = FD_SUP, v = null;
                var i, len, b;
                for (i = 0, len = varnames.length; i < len; ++i) {
                    b = domain_bounds(S.vars[varnames[i]].dom);
                    if (b[1] - b[0] <= ds && b[1] > b[0]) {
                        v = varnames[i];
                        ds = b[1] - b[0];
                    }
                }
                return v;
            }

            var branch_sequence = {
                branch: function (S) {
                    var state, v, dom;
                    if (!S.__branch_state) {
                        v = var_with_smallest_domain();
                        if (v) {
                            dom = S.vars[v].dom;
                            state = S.__branch_state = {
                                var: v,
                                dom: dom,
                                i: 0,
                                val: dom[0][0]
                            };
                            if (varnames.length > 1) {
                                Distribute.fail_first(S, varnames.filter(function (n) { return n !== v; }));
                            }
                        } else {
                            return null;
                        }
                    } else {
                        state = S.__branch_state;
                        v = state.var;
                        dom = state.dom;
                    }

                    if (state.val > dom[state.i][1]) {
                        state.i++;
                        if (state.i >= dom.length) {
                            return null;
                        } else {
                            state.val = dom[state.i][0];
                        }
                    }

                    var Sc = S.clone();
                    var vc = Sc.vars[state.var];
                    vc.set_dom([[state.val, state.val]]);
                    state.val++;
                    return Sc;
                }
            };

            S.brancher.enqueue(branch_sequence);
            return S;
        }
    };

    // Search using the branchers.
    var Search = {};

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
        var brancher, next_space;

        // If no stack argument, then search begins with this space.
        if (!stack || stack.length === 0) {
            stack = state.stack = [space];
        }

        while (stack.length > 0) {
            space = stack[stack.length - 1];

            try {
                // Wait for stability. Could throw a 'fail', in which case
                // this becomes a failed space.
                space.propagate();

                if (space.is_solved()) {
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
                next_space = space.brancher.branch();
                if (next_space) {
                    // Push on to the stack and explore further.
                    stack.push(next_space);
                } else {
                    // Finished exploring branches of this space. Continue with the previous spaces.
                    // This is a stable space, but isn't a solution. Neither is it a failed space.
                    stack.pop();
                    state.more = stack.length > 0;
                }
            } catch (e) {
                // Some propagators failed so this is now a failed space and we need
                // to pop the stack and continue from above. This is a failed space.
                space.failed = true;
                stack.pop();
            }
        }

        // Failed space and no more options to explore.
        state.status = 'end';
        state.more = false;
        return state;
    };

    exports.SUP = FD_SUP;
    exports.INF = 0;
    exports.space = Space;
    exports.distribute = Distribute;
    exports.search = Search;

    return exports;
})({}, Math);
