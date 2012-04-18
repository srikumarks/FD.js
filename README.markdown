`fd.js` is a Javascript finite domain constraint programming (CP) library with
a design based on the CP features of [Mozart/Oz]. In particular, `fd.js` aims to
separate the concerns of constraint problem specification, branching strategy
and search strategy through the use of "computation spaces".

## Status

Work *very much* in progress, but the library is already useful enough to solve
simple puzzles.

## Related links

* [Mozart/Oz]
* [Gecode]

## License

All source code part of the `fd.js` project is licensed under the permissive [New BSD license].

------------------------
# API
------------------------

## FD

This is the top level "module" that you get when you load fd.js.

## FD.space 

"Computation space" class holding variables and propagators.  You create a new
"computation space" by doing -

    var S = new FD.space();

##### S.clone()

Creates a "clone" of the space S. Further computations carried out in the clone
do not affect S.

##### S.propagate()

Runs all propagators until no more can run - i.e. until the space becomes
"stable" or "failed". Propagators fail by throwing a "fail" exception. So if
this call returns, you've got a stable space.

##### S.is_solved()

Checks all the fd vars in the space and returns true if all of them have
singleton domains and false otherwise.

##### S.inject(script)

Calls script(S) so that the script can add propagators to the space and any
needed branchers. Returns S.

##### S.decl(name_or_names, dom?)

Declares the given named fd vars. If dom is specified, initializes the domains
of all of them to the given domain. A domain is specified as an array of
intervals like this -
    
    [[10,20],[100,133],[1729,3551]]

The sub-intervals should not overlap and must be in increasing order. Both the
bounds of each sub-interval are considered to be included in the domain.
Returns S.

##### S.temp(dom?) and S.temps(N, dom?)

Creates new temporary or intermediate fd variables whose names you don't want
to bother with. Returns the name of the temporary variable.  

##### S.const(n)

Currently shorthand for `S.temp([[n, n]])`. Might be optimized in the future.

## Propagators

Propagators are provided as method invocations on a space and all such calls
return the space itself as the result so that further method invocations can be
concatenated.

##### S.eq(v1name, v2name)

Asserts that fd variable named `v1name` is equal to that named `v2name`.  

##### S.lt(v1name, v2name) 

Asserts that fd variable `v1` is strictly less than `v2`.

##### S.gt(v1name, v2name) 

Asserts that fd variable `v1` is strictly greater
than `v2`.  

##### S.lte(v1name, v2name) 

Asserts that fd variable `v1` is less than or equal to `v2`.  

##### S.gte(v1name, v2name) 

Asserts that fd variable `v1` is greater than or equal to `v2`.  

##### S.neq(v1name, v2name) 

Asserts that fd variables `v1` and `v2` must be different.  

##### S.distinct(names)

Asserts that all the variables in the given array are pair-wise distinct.

##### S.plus(v1name, v2name, sumname) 

Asserts `v1 + v2 = sum` and propagates domain changes to all three fd vars.  

##### S.times(v1name, v2name, prodname)

Asserts `v1 * v2 = prod` and propagates domain changes to all three fd vars.

##### S.scale(factor, vname, prodname) 

Asserts `factor * v = prod + v2 = sum` and propagates domain changes to both fd
vars. factor has to be a constant and not an fd var.  

##### S.times_plus(k1, v1name, k2, v2name, resultname) 

Asserts `k1 * v1 + k2 * v2 = result`. `k1` and `k2` have to be constants and
not fd vars.  

##### S.sum(vnames, sumname) 

Asserts that the sum of all the variables in the given vnames array equals the
sumname variable.  

##### S.product(vnames, prodname) 

Asserts that the product of all the variables in the given vnames array equals
the prodname variable.  

##### S.wsum(kweights, vnames, sumname)

`kweights` is an array of constant natural numbers and `vnames` is an array of
fd var names of the same length as kweights. This then adds propagators that
ensure that the weighted sum of these variables equals the given sum variable.

##### S.reified(opname, argv, boolname) 

Provides support for reified propagators. Currently only the various comparison
propagators are supported - i.e. opname can be one of 'eq', 'lt', 'gt', 'lte'
or 'gte' only. Any other value will throw an exception. `argv` must be an array
of variable names to which the comparison is applied. `boolname` must be the
name of a declared fdvar that will be constrained to take on either 0 or 1. If
`boolname` is omitted, then a temporary variable is allocated and returned as
the result, thus permitting `reified` to be used with "functional notation".
See the `test_mozart_photo_bab` example for use of reified comparison
propagators. For example, to reify the comparison X < Y as the boolean variable
Z, do this -

    S.reified('lt', ['X', 'Y'], 'Z');

### Functional notation

Propagator methods such as plus, times, sum and wsum take the "result variable"
as the last argument. Quite often, you'll need to create an intermediate (i.e.
"temporary") variable to hold a result. To make that easier, omitting the last
result argument will cause the propagator method to automatically create a
temporary for the result and return the name of the created temporary instead
of the space on which the method was invoked. This lets us use a convenient
"functional" syntax. For an example, see the test_send_more_money_fn script in
tests.js and compare it with the test_send_more_money script.

## FD.distribute 

A namespace that holds various distribution strategies.

##### FD.distribute.naive(S, varname) 

Walks through the values in the do main of the specified variable. varname can
also be an array of variable names in which case the "naive" call will
automatically run for each of the given variables in sequence. This
auto-mapping behaviour is for programming convenience.  

##### FD.distribute.fail_first(S, varnames) 

Given an array of variable names, figures out the one with the smallest domain
and branches on it first, then moving on to the immediately larger domain, and
so on.  

##### FD.distribute.split(S, varname) 

Adds branchers that split the domain of the specified fdvar (or variables, if
an array or an object with fdvars was supplied) into pieces for each branch. A
variable's domain is first split at the holes and once it has no holes, it is
split down the middle.  

## FD.search 

A namespace that holds various search strategies.

##### FD.search.depth_first(state)

Implements the "depth first" search strategy. `state` is expected to be an
object whose `space` property is the starting space for the search. The state
object is also the return value, but with additional properties filled in. On
return, if `state.status` is the string `"solved"`, then `state.space` is a
solution. If there may be more solutions, then `state.more` will be `true`. If
no solution space is found even after considering branchers, then
`state.status` will be set to `"end"` upon return and state.more will be
`false`. If you want to get all possible solutions, then you need to
iteratively call `depth_first` passing the returned state of one call as the
argument of the next call and collect all the cases where `state.status` is
`"solved"`.

##### FD.search.branch_and_bound(state, ordering)

Finds the "best" solution according to the given ordering function. The `state`
parameter is similar to the `depth_first` search function. It is expected to be
an object such that `state.space` gives the space from which to search for the
best solution.

The `state` is also what is returned by `branch_and_bound` and `state.space`
will be the space with the best solution found during the search. When a
solution exists, `state.status` will be the string "solved".

The `ordering` argument is expected to be a function of the form

    function (space, a_solution) { ... }

where the `space` argument is the space into which the ordering function should
inject the new constraints for the ordering, and `a_solution` is an object
whose keys are root finite domain variable names and whose values are the
solved values of those variables. The return value of the ordering function is
irrelevant.

There are two ways to use the branch_and_bound function -

In one shot mode where a single call will give you the best solution that it
can find, if a solution exists at all.

In "single step" mode, indicated by setting `state.single_step` to `true`. In
this mode, the function will return whenever it finds a solved space and
`state.more` will indicate whether there may be any more solutions to look at.
In this mode, every call will result in a solution that is "better" than the
one found before it, due to the `ordering` function.

Note that if `state.more` is `false`, then definitely there are no more
solutions to look at, but if it is `true`, there *may* be more solutions to
look at. If a subsequent search turns up empty, it is indicated by
`state.status` being set to the string "end".


[Mozart/Oz]: http://www.mozart-oz.org/ (The Mozart Programming System)
[Gecode]: http://www.gecode.org/ (Gecode: Generic Constraint Development Environment)
[New BSD license]: http://www.opensource.org/licenses/bsd-license.php

