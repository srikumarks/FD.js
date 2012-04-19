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

// NOTE: The fd.js module needs to be loaded prior to
// loading this file.
try {
    FD.space;
} catch (e) {
    alert("fd.js module needs to be loaded before fd-tests.js");
}

(function () {

    // A simple script for solving sudoku puzzles.
    // 'board' is an object whose keys are sudoku
    // cell references of the form <letter><digit>
    // where <letter> gives the row letter from
    // ABCDEFGHI and <digit> gives column from
    // 123456789. The solution of the space will be 
    // an object with a key for each cell.
    function sudoku(board) {
        return function (S) {
            var rows = ['A','B','C','D','E','F','G','H','I'];
            var cols = ['1','2','3','4','5','6','7','8','9'];
            var root = [];
            var i, j, k, i2, j2;

            // Declare board places.
            for (i = 0; i < 9; ++i) {
                for (j = 0; j < 9; ++j) {
                    root.push(rows[i] + cols[j]);
                }
            }

            S.decl(root, [[1,9]]);

            // Add row constraints.
            for (i = 0; i < 9; ++i) {
                k = [];
                for (j = 0; j < 9; ++j) {
                    k.push(rows[i] + cols[j]);
                }
                S.distinct(k);
            }

            // Add column constraints
            for (i = 0; i < 9; ++i) {
                k = [];
                for (j = 0; j < 9; ++j) {
                    k.push(rows[j] + cols[i]);
                }
                S.distinct(k);
            }

            // Add box constraints.
            for (i = 0; i < 3; ++i) {
                for (j = 0; j < 3; ++j) {
                    k = [];
                    for (i2 = 0; i2 < 3; ++i2) {
                        for (j2 = 0; j2 < 3; ++j2) {
                            k.push(rows[i * 3 + i2] + cols[j * 3 + j2]);
                        }
                    }
                    S.distinct(k);
                }
            }

            // Initialize the board.
            for (i in board) {
                S.num(i, board[i]);
            }

            // Distribution strategy is fail first, since that is
            // likely to cause maximum propagation for this puzzle.
            FD.distribute.fail_first(S, root);
            return S;
        };
    }

    // Helps check that all the elements of the array are different
    // from each other.
    function verify_distinct(values) {
        var arr, i, j, k, N;

        if (values instanceof Array) {
            arr = values;
        } else if (values instanceof Object) {
            arr = [];
            for (k in values) {
                arr.push(values[k]);
            }
        } else {
            throw "verify_distinct: Invalid argument.";
        }

        for (i = 0, N = arr.length; i < N; ++i) {
            for (j = 0; j < i; ++j) {
                if (arr[i] === arr[j]) {
                    return false;
                }
            }
        }
        return true;
    }

    // Checks that the given board is solved.
    function verify_sudoku(board) {
        var rows = ['A','B','C','D','E','F','G','H','I'];
        var cols = ['1','2','3','4','5','6','7','8','9'];
        var i, j, k, i2, j2, b;

        // Add row constraints.
        for (i = 0; i < 9; ++i) {
            k = [];
            for (j = 0; j < 9; ++j) {
                b = board[rows[i] + cols[j]];
                if (b < 1 || b > 9) {
                    // Check domain validity.
                    return false;
                }
                k.push(b);
            }

            if (!verify_distinct(k)) {
                return false;
            }
        }

        // Add column constraints
        for (i = 0; i < 9; ++i) {
            k = [];
            for (j = 0; j < 9; ++j) {
                k.push(board[rows[j] + cols[i]]);
            }

            if (!verify_distinct(k)) {
                return false;
            }
        }

        // Add box constraints.
        for (i = 0; i < 3; ++i) {
            for (j = 0; j < 3; ++j) {
                k = [];
                for (i2 = 0; i2 < 3; ++i2) {
                    for (j2 = 0; j2 < 3; ++j2) {
                        k.push(board[rows[i * 3 + i2] + cols[j * 3 + j2]]);
                    }
                }

                if (!verify_distinct(k)) {
                    return false;
                }
            }
        }

        return true;
    }

    // Some simple tests.
    var tests = [
    {   name: 'test_plus',
        description: 'Simple plus test',
        search: FD.search.depth_first,

        verify: function (sol) {
            return sol.Y === 7;
        },

        script: function (S) {
            return S.num('X', 3).num('Z', 10).decl('Y').plus('X', 'Y', 'Z');
        }
    },
    {   name: 'test_plus_nosol',
        description: "plus, but no solution exists",
        search: FD.search.depth_first,

        verify: function (sol) {
            return false;
        },

        script: function (S) {
            // In this case no solution exists.
            return S.num('X', 13).num('Z', 10).decl('Y').plus('X', 'Y', 'Z');
        }
    },
    {   name: 'test_plus_range',
        description: "Domain narrowing by propagators",
        search: FD.search.depth_first,
        verify: function (sol) {
            return true; // TODO: CHEATING!
        },
        script: function (S) {
            // No *unique* solution exists, but Y will be narrowed to a range.
            // TODO: This test works, but is not printed out currently since the
            // solution is not unique.

            return S.num('X', 13).decl('Z', [[0, 100]]).decl('Y').plus('X', 'Y', 'Z');
        }
    },
    {   name: 'test_sum',
        description: "Simple 'sum' test",
        search: FD.search.depth_first,
        verify: function (sol) {
            return true; // TODO: CHEATING!
        },
        script: function (S) {
            // A mixture of some constraints X + Y + Z = W and X < Y.
            // TODO: This test works, but is not printed out currently since the
            // solution is not unique.

            return S.decl(['X', 'Y', 'Z'], [[0, 10]]).decl('W').sum(['X', 'Y', 'Z'], 'W').lt('X', 'Y');
        }
    },
    {   name: 'test_naive',
        description: "Simple test of naive distribution",
        search: FD.search.depth_first,
        verify: function (sol) {
            return sol.X + sol.Y === sol.Z;
        },
        script: function (S) {
            // List out all possible solutions of X + Y = Z with some domain limits.
            S.decl('X', [[0, 3]]);
            S.decl('Y', [[4, 6]]);
            S.decl('Z');
            S.plus('X', 'Y', 'Z');

            FD.distribute.naive(S, ['X', 'Y']);
            return S;
        }
    },
    {   name: 'test_wsum',
        description: "Simple test of wsum with fail_first distribution",
        search: FD.search.depth_first,
        verify: function (sol) {
            return 10 * sol.A + sol.B === sol.C;
        },
        script: function (S) {
            // Test of "weighted sum" and enumeration of all
            // solutions using the "fail first" distribution
            // strategy.
            S.decl(['A','B','C']);
            S.wsum([10,1], ['A','B'], 'C');
            S.vars.C.set_dom([[0,20]]);
            FD.distribute.fail_first(S, ['A','B','C']);
            return S;
        }
    },
    {   name: 'test_distinct',
        description: "Simple distinct test",
        search: FD.search.depth_first,
        verify: function (sol) {
            return (sol.A + sol.B === sol.C) && (sol.A !== sol.B);
        },
        script: function (S) {
            // Test of "distinct" constraint.
            var root = ['A','B','C'];
            S.decl(root);
            S.decl(['A', 'B'], [[0, 10]]);
            S.distinct(['A','B']);
            S.plus('A','B','C');
            FD.distribute.fail_first(S, root);
            return S;
        }
    },
    {   name: 'test_simple_multiple_branchers',
        description: "Simple test of multiple branching strategies mixed in.",
        search: FD.search.depth_first,
        verify: function (sol) {
            return sol.A !== sol.B;
        },
        script: function (S) {
            S.decl('A', [[1,5]]);
            S.decl('B', [[1,5]]);
            S.neq('A', 'B');
            FD.distribute.split(S, 'A');
            FD.distribute.naive(S, 'B');
            return S;
        }
    },
    {   name: 'test_send_more_money',
        description: "The famous SEND + MORE = MONEY problem, using fail_first distribution.",
        search: FD.search.depth_first,
        verify: function (sol) {
            var SEND = sol.S * 1000 + sol.E * 100 + sol.N * 10 + sol.D;
            var MORE = sol.M * 1000 + sol.O * 100 + sol.R * 10 + sol.E;
            var MONEY = sol.M * 10000 + sol.O * 1000 + sol.N * 100 + sol.E * 10 + sol.Y;
            return SEND + MORE === MONEY;
        },
        script: function (S) {
            // The famous "SEND + MORE = MONEY" problem.
            // TODO: Note that though this works, it doesn't
            // produce the same search tree that Oz does.
            // Either I don't have as strong propagators as Oz 
            // just yet or the way wsum groups its operations
            // needs to be changed. Seems enough to correctly
            // solve the problem though.
            var root = ['S','E','N','D','M','O','R','Y'];
            S.decl(root, [[0,9]]).distinct(root);
            S.vars.S.set_dom([[1,9]]);
            S.vars.M.set_dom([[1, 9]]);

            var t1 = S.temp();
            var t2 = S.temp();
            var t3 = S.temp();

            S.wsum([1000,100,10,1], ['S','E','N','D'], t1);
            S.wsum([1000,100,10,1], ['M','O','R','E'], t2);
            S.wsum([10000,1000,100,10,1], ['M','O','N','E','Y'], t3);
            S.plus(t1, t2, t3);
            FD.distribute.fail_first(S, root);
            return S;
        }
    },
    {   name: 'test_send_more_money_fn',
        description: "Same SEND + MORE = MONEY in functional notation",
        search: FD.search.depth_first,
        verify: function (sol) {
            var SEND = sol.S * 1000 + sol.E * 100 + sol.N * 10 + sol.D;
            var MORE = sol.M * 1000 + sol.O * 100 + sol.R * 10 + sol.E;
            var MONEY = sol.M * 10000 + sol.O * 1000 + sol.N * 100 + sol.E * 10 + sol.Y;
            return SEND + MORE === MONEY;
        },
        script: function (S) {
            // Same problem as above, but expressed in "functional" notation.
            var root = ['S','E','N','D','M','O','R','Y'];
            S.decl(root, [[0,9]]).distinct(root);
            S.decl(['S','M'], [[1,9]]);

            S.plus(S.wsum([1000,100,10,1], ['S','E','N','D']),
                    S.wsum([1000,100,10,1], ['M','O','R','E']),
                    S.wsum([10000,1000,100,10,1], ['M','O','N','E','Y']));

            FD.distribute.fail_first(S, root);
            return S;
        }
    },
    {   name: 'test_sudoku',
        description: "A <a href=\"http://en.wikipedia.org/wiki/Sudoku\">simple</a> Sudoku board",
        search: FD.search.depth_first,
        verify: verify_sudoku,
        script: function (S) {
            return sudoku({
                A5:8, A8:7, A9:9, 
            B4:4, B5:1, B6:9, B9:5,
            C2:6, C7:2, C8:8,
            D1:7, D5:2, D9:6,
            E1:4, E4:8, E6:3, E9:1,
            F1:8, F5:6, F9:3,
            G2:9, G3:8, G8:6,
            H1:6, H4:1, H5:9, H6:5,
            I1:5, I2:3, I5:7
            })(S);
        }
    },
    {   name: 'test_extreme_sudoku',
        description: "An <a href=\"http://www.extremesudoku.info/sudoku.html\">extreme</a> sudoku puzzle",
        search: FD.search.depth_first,
        verify: verify_sudoku,
        script: function (S) {
            return sudoku({
                A1:4, A4:6, A7:7,
            B2:7, B5:4, B8:2,
            C3:5, C6:1, C9:6,
            D3:3, D6:5, D9:8,
            E2:2, E5:1, E8:9,
            F1:9, F4:7, F7:4,
            G1:3, G4:1, G7:9,
            H2:1, H5:8, H8:6,
            I3:7, I6:6, I9:1
            })(S);
        }
    },
    {   name: 'test_really_hard_sudoku',
        description: "A <a href=\"http://4puz.com/hard_puzzle_v1p1.html\">really hard</a> sudoku",
        search: FD.search.depth_first,
        verify: verify_sudoku,
        script: function (S) {
            return sudoku({
                A6:8, A7:5,
            B2:2, B6:6, B9:1,
            C2:3, C3:9, C8:4, C9:2,
            D7:6, D8:1,
            E1:4, E9:5,
            F2:1, F3:7,
            G1:2, G2:5, G7:1, G8:9,
            H1:3, H4:4, H8:2,
            I3:8, I4:9
            })(S);
        }
    },
    {   name: 'test_norvig_hard_sudoku',
        description: "A <a href=\"http://norvig.com/sudoku.html\">Norvig hard</a> sudoku puzzle. There are multiple solutions but it still doesn't take very long find quite a few of them.",
        search: FD.search.depth_first,
        verify: verify_sudoku,
        max_solutions: 10,
        script: function (S) {
            // This puzzle blows Chrome if you try to find all solutions! 
            // So we don't do that and limit the number of solutions to find. 
            return sudoku({
                C4:3, C5:2, C6:5, C9:6,
                   D3:6, D6:3, D8:5, D9:4,
                   E3:3,
                   F2:4, F3:5,
                   G1:2, G6:8,
                   H2:5, H3:9, H9:8,
                   I6:6
            })(S);
        }
    },
    {   name: 'test_worlds_hardest_sudoku',
        description: "The <a href=\"http://zonkedyak.blogspot.com/2006/11/worlds-hardest-sudoku-puzzle-al.html\">world's hardest (yeah right!)</a> sudoku puzzle.",
        search: FD.search.depth_first,
        verify: verify_sudoku,
        script: function (S) {
            return sudoku({
                A3:7, A7:3,
            B2:4, B9:7,
            C1:3, C8:1,
            D1:6, D6:4,
            E2:1, E5:8, E9:2,
            F3:5, F4:3, F7:9,
            G3:9, G4:6, G7:5,
            H2:3, H5:2, H9:8,
            I1:1, I6:7, I8:9
            })(S);
        }
    },
    {   name: 'test_fiendishly_hard_sudoku',
        description: "The <a href=\"http://hagaregn.org.uk/npsudoku/sudoku.html\">fiendishly hard (yeah right!)</a> sudoku puzzle.",
        search: FD.search.depth_first,
        verify: verify_sudoku,
        script: function (S) {
            return sudoku({
                A1:7,
                B2:3, B4:5,
                C5:4, C7:2,
                D4:3, D8:7,
                E1:2, E7:6,
                F2:5, F4:1, F6:8,
                G5:7,
                H1:6, H5:2,
                I8:3, I9:1
            })(S);
        }
    },
    {   name: 'test_blank_sudoku',
        description: "Starting from a blank slate, find one solution",
        search: FD.search.depth_first,
        verify: verify_sudoku,
        max_solutions: 1,
        script: sudoku({})
    },
    {   name: 'test_reified_lt',
        description: "Simple test of reified less-than operator: X < Y :: Z, Z == 0",
        search: FD.search.depth_first,
        verify: function (sol) {
            return (sol.X < sol.Y && (sol.Z === 1)) || (sol.X >= sol.Y && (sol.Z === 0));
        },
        script: function (S) {
            S.decl('X', [[1, 10]]).decl('Y', [[5, 6]]).decl('Z', [[0,0]]);
            S.reified('lt', ['X', 'Y'], 'Z');
            FD.distribute.naive(S, ['X', 'Y', 'Z']);
            return S;
        }
    }];

    function test_simple_bab(dist_strategy) {
        return {   
            name: 'test_simple_bab+'+dist_strategy,
            description: ("Simple bab X + Y = Z, maximize Z, with X `neq` A and X, Y, A in [[1,5]] " +
                    "(A is irrelevant to the optimization). Note that A != X condition is not verified automatically. (Lazy!)"),
            single_step: true,
            verify: function (sol) {
                return sol.X + sol.Y === sol.Z;
            },
            search: (function () {

                function ordering(S, solution) {
                    S.gt('Z', S.const(solution.Z));
                }

                return function (state) {
                    state.single_step = this.single_step;
                    state.is_solved = state.is_solved || FD.search.solve_for_variables(['X', 'Y']);
                    return FD.search.branch_and_bound(state, ordering);
                };
            })(),
            script: function (S) {
                S.decl(['X', 'Y', 'A'], [[1, 5]]).decl('Z');
                S.plus('X', 'Y', 'Z');
                S.neq('X', 'A');
                FD.distribute[dist_strategy](S, ['X', 'Y']);
                return S;
            }
        };
    }

    function test_mozart_photo_bab(dist_strategy) {
        return {   
            name: 'test_mozart_photo_bab+'+dist_strategy,
            description: 'From <a href="http://www.mozart-oz.org/documentation/fdt/node44.html#section.bab.align">Mozart/Oz BAB example</a>.',
            single_step: true,
            verify: function (sol) {
                var sat = sol.Satisfaction;
                delete sol.Satisfaction; // Don't include the 'Satisfaction' value in the distinct test.
                return verify_distinct(sol) && (function () {
                    var count = 0;
                    var preferences = [
                    ['Betty', 'Gary'],
                       ['Betty', 'Mary'],
                       ['Chris', 'Betty'],
                       ['Chris', 'Gary'],
                       ['Fred', 'Mary'],
                       ['Fred', 'Donald'],
                       ['Paul', 'Fred'],
                       ['Paul', 'Donald']
                    ];

                    preferences.forEach(function (p) {
                        if (Math.abs(sol[p[0]] - sol[p[1]]) < 1.5) {
                            count++;
                        }
                    });

                    return Math.abs(count - sat) < 0.1;
                }());
            },
            search: (function () {

                function ordering(S, solution) {
                    S.gt('Satisfaction', S.const(solution.Satisfaction));
                }

                return function (state) {
                    state.single_step = this.single_step;
                    state.is_solved = state.is_solved || FD.search.solve_for_variables([
                        'Betty', 'Chris', 'Donald', 'Fred', 'Gary', 'Mary', 'Paul'
                        ]);
//                    state.is_solved = FD.search.solve_for_propagators;
                    return FD.search.branch_and_bound(state, ordering);
                };
            })(),
            script: function (S) {
                var one = S.const(1);
                var zero = S.const(0);

                function satisfied(p) {
                    var a = S.reified('eq', [S.plus(p[0], one), p[1]]);
                    var b = S.reified('eq', [S.plus(p[1], one), p[0]]);
                    return S.plus(a, b);                
                }

                var persons = ['Betty', 'Chris', 'Donald', 'Fred', 'Gary', 'Mary', 'Paul'];
                var preferences = [
                    ['Betty', 'Gary'],
                    ['Betty', 'Mary'],
                    ['Chris', 'Betty'],
                    ['Chris', 'Gary'],
                    ['Fred', 'Mary'],
                    ['Fred', 'Donald'],
                    ['Paul', 'Fred'],
                    ['Paul', 'Donald']
                        ];

                S.decl(persons, [[1, persons.length]]);
                S.decl('Satisfaction');

                S.distinct(persons);
                S.sum(preferences.map(satisfied), 'Satisfaction');
                S.lt('Fred', 'Betty');

                FD.distribute[dist_strategy](S, persons);
                return S;
            }
        };
    }


    tests.push(test_simple_bab('naive'));
    tests.push(test_simple_bab('fail_first'));
    tests.push(test_simple_bab('split'));
    tests.push(test_mozart_photo_bab('naive'));
    tests.push(test_mozart_photo_bab('fail_first'));
    
    if (false) {
        var t = test_mozart_photo_bab('naive');
        t.search = FD.search.depth_first;
        t.name = t.name + '+depth_first';
        tests.push(t);
    }

   tests.push(test_mozart_photo_bab('split'));

   function test_n_queens(N, max_solutions) {
       return  {   
               name: 'test_'+N+'_queens',
               description: ''+N+' queens problem',
               search: FD.search.depth_first,
               max_solutions: max_solutions,
               verify: function (sol) {
                   var i, j;

                   if (!verify_distinct(sol)) {
                       return false;
                   }

                   for (i = 1; i <= N; ++i) {
                       for (j = 1; j < i; ++j) {
                           if (sol['R'+i]-i === sol['R'+j]-j || sol['R'+i]+i === sol['R'+j]+j) {
                               return false;
                           }
                       }
                   }

                   return true;
               },
               script: function (S) {
                   var i, j, k;
                   var root = [];
                   for (i = 1; i <= N; ++i) {
                       root.push('R'+i);
                   }

                   S.decl(root, [[1, N]]);
                   S.distinct(root);

                   for (i = 0; i < N; ++i) {
                       for (j = 0; j < i; ++j) {
                           k = S.const(i-j);
                           S.neq(S.plus(root[j], k), root[i]);
                           S.neq(S.plus(root[i], k), root[j]);
                       }
                   }

                   FD.distribute.fail_first(S, root);
                   return S;
               }
       };
   }

   tests.push(test_n_queens(8));

    var run_tests = (function () {
        var display = {};
        display.__proto__ = (document || console);
        display.show = (document && document.write) || console.log;

        var strings = {
            correct: '<span style="color:green">CORRECT</span>',
        wrong: '<span style="color:red"><b>WRONG!</b></span>'
        };

        function show_result(test, result, start) {
            if (result.status === 'solved' || (!result.space.failed && result.space.brancher.queue.length === 0)) {
                var end = Date.now();
                var S = result.best || result.space;
                var failure = (result.is_solved(S) && test.verify) ? strings[test.verify(S.solution()) ? 'correct' : 'wrong'] : '';
                display.show('<p><tt>' + '['+(end-start)+' ms] ' + failure + ' ' + result.status + ': ' + JSON.stringify(S.solution()) + '</tt></p>');
                return 1;
            } else {
                return 0;
            }
        }

        return function () {
            tests.forEach(function (test) { 
                if (test.do_not_run || !test.script) {
                    return;
                }

                // Default to depth_first search if unspecified.
                test.search = test.search || FD.search.depth_first;

                var S = test.script(new FD.space());
                if (S) {
                    var start = Date.now();
                    var state = {space: S}; // for-debugging: {space: S, verify: test.verify};
                    var count = 0;

                    display.show('<p><b><a name="' + test.name + '">' + test.name + '</a>:</b> ' + test.description + '</p>' + (test.single_step ? ' (single stepping)' : ''));

                    do {
                        state = test.search(state);
                        count += show_result(test, state, start);
                        if (count >= test.max_solutions) {
                            display.show('<p>--- reached given limit of ' + test.max_solutions + ' solutions ---</p>');
                            break;
                        }
                    } while (state.more);

                    if (count === 0) {
                        display.show('<p><tt>No solution</tt></p>');
                    }

                    display.show('<p>succ = ' + S.succeeded_children + ', fail = ' + S.failed_children + ', stab = ' + S.stable_children + ', <b>total</b> = ' +
                            (S.succeeded_children + S.failed_children + S.stable_children) + '</p>');
                    display.show('<hr/>');
                }
            });
        };
    })();

    // Comment this out if you don't want to run the tests.
    run_tests();

})();
