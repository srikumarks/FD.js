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

    // Some simple tests.
    var tests = [
         function test_plus(S) {
             // Very simple "X + Y = Z, solve for Y" test.
             test_plus.description = "Simple plus test";
             return S.num('X', 3).num('Z', 10).decl('Y').plus('X', 'Y', 'Z');
         },
         function test_plus_nosol(S) {
             // In this case no solution exists.
             test_plus_nosol.description = "plus, but no solution exists";
             return S.num('X', 13).num('Z', 10).decl('Y').plus('X', 'Y', 'Z');
         },
         function test_plus_range(S) {
             // No *unique* solution exists, but Y will be narrowed to a range.
             // TODO: This test works, but is not printed out currently since the
             // solution is not unique.
             test_plus_range.description = "Domain narrowing by propagators";
             return S.num('X', 13).decl('Z', [[0, 100]]).decl('Y').plus('X', 'Y', 'Z');
         },
         function test_sum(S) {
             // A mixture of some constraints X + Y + Z = W and X < Y.
             // TODO: This test works, but is not printed out currently since the
             // solution is not unique.
             test_sum.description = "Simple 'sum' test";
             return S.decl(['X', 'Y', 'Z'], [[0, 10]]).decl('W').sum(['X', 'Y', 'Z'], 'W').lt('X', 'Y');
         },
         function test_naive(S) {
             // List out all possible solutions of X + Y = Z with some domain limits.
             test_naive.description = "Simple test of naive distribution";
             S.decl('X', [[0, 3]]);
             S.decl('Y', [[4, 6]]);
             S.decl('Z');
             S.plus('X', 'Y', 'Z');

             FD.distribute.naive(S, ['X', 'Y']);
             return S;
         },
         function test_wsum(S) {
             // Test of "weighted sum" and enumeration of all
             // solutions using the "fail first" distribution
             // strategy.
             test_wsum.description = "Simple test of wsum with fail_first distribution";
             S.decl(['A','B','C']);
             S.wsum([10,1], ['A','B'], 'C');
             S.vars.C.set_dom([[0,20]]);
             FD.distribute.fail_first(S, ['A','B','C']);
             return S;
         },
         function test_distinct(S) {
             // Test of "distinct" constraint.
             test_distinct.description = "Simple distinct test";
             var root = ['A','B','C'];
             S.decl(root);
             S.decl(['A', 'B'], [[0, 10]]);
             S.distinct(['A','B']);
             S.plus('A','B','C');
             FD.distribute.fail_first(S, root);
             return S;
         },
         function test_send_more_money(S) {
             // The famous "SEND + MORE = MONEY" problem.
             // TODO: Note that though this works, it doesn't
             // produce the same search tree that Oz does.
             // Either I don't have as strong propagators as Oz 
             // just yet or the way wsum groups its operations
             // needs to be changed. Seems enough to correctly
             // solve the problem though.
             test_send_more_money.description = "The famous SEND + MORE = MONEY problem, using fail_first distribution.";
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
         },
         function test_send_more_money_fn(S) {
             // Same problem as above, but expressed in "functional" notation.
             test_send_more_money_fn.description = "Same SEND + MORE = MONEY in functional notation";

             var root = ['S','E','N','D','M','O','R','Y'];
             S.decl(root, [[0,9]]).distinct(root);
             S.decl(['S','M'], [[1,9]]);

             S.plus(S.wsum([1000,100,10,1], ['S','E','N','D']),
                     S.wsum([1000,100,10,1], ['M','O','R','E']),
                     S.wsum([10000,1000,100,10,1], ['M','O','N','E','Y']));

             FD.distribute.fail_first(S, root);
             return S;
         },
         function test_sudoku(S) {
             test_sudoku.description = "A <a href=\"http://en.wikipedia.org/wiki/Sudoku\">simple</a> Sudoku board";
             return sudoku({A5:8, A8:7, A9:9, 
                 B4:4, B5:1, B6:9, B9:5,
                    C2:6, C7:2, C8:8,
                    D1:7, D5:2, D9:6,
                    E1:4, E4:8, E6:3, E9:1,
                    F1:8, F5:6, F9:3,
                    G2:9, G3:8, G8:6,
                    H1:6, H4:1, H5:9, H6:5,
                    I1:5, I2:3, I5:7})(S);
         },
         function test_extreme_sudoku(S) {
             test_extreme_sudoku.description = "An <a href=\"http://www.extremesudoku.info/sudoku.html\">extreme</a> sudoku puzzle";
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
         },
         function test_really_hard_sudoku(S) {
             test_really_hard_sudoku.description = "A <a href=\"http://4puz.com/hard_puzzle_v1p1.html\">really hard</a> sudoku";
             debugger;
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
         },
         function test_norvig_hard_sudoku(S) {
             test_norvig_hard_sudoku.description = "A <a href=\"http://norvig.com/sudoku.html\">Norvig hard</a> sudoku puzzle (blows up Chrome!).";
             // This puzzle blows Chrome! So we don't do it. It also has multiple solutions and is
             // therefore not a true sudoku puzzle.
             return S;
             return sudoku({
                 C4:3, C5:2, C6:5, C9:6,
                    D3:6, D6:3, D8:5, D9:4,
                    E3:3,
                    F2:4, F3:5,
                    G1:2, G6:8,
                    H2:5, H3:9, H9:8,
                    I6:6
             })(S);
         },
         function test_worlds_hardest_sudoku(S) {
             test_worlds_hardest_sudoku.description = "The <a href=\"http://zonkedyak.blogspot.com/2006/11/worlds-hardest-sudoku-puzzle-al.html\">world's hardest (yeah right!)</a> sudoku puzzle.";
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
    ];

    var run_tests = (function () {
        var stable_count = [];

        var display = {};
        display.__proto__ = (document || console);
        display.show = (document && document.write) || console.log;

        function flush_stable_count() {
            if (stable_count.length > 0) {
                console.log(stable_count.join(''));
                stable_count = [];
            }
        }

        function show_result(result, start) {
            if (result.status === 'solved' || (!result.space.failed && result.space.brancher.queue.length === 0)) {
                var end = Date.now();
                display.show('<p><tt>' + '['+(end-start)+' ms] ' + result.status + ': ' + JSON.stringify(result.space.solution()) + '</tt></p>');
                return 1;
            } else {
                return 0;
            }
        }

        return function () {
            tests.forEach(function (script) { 
                var S = script(new FD.space());
                if (S) {
                    var start = Date.now();
                    var state = {space: S};
                    var count = 0;
                    display.show('<p><b>' + script.name + ':</b> ' + script.description + '</p>');
                    do {
                        state = FD.search.depth_first(state);
                        count += show_result(state, start);
                    } while (state.more);
            if (count === 0) {
                display.show('<p><tt>No solution</tt></p>');
            }
            display.show('<hr/>');
                }
            });
        };
    })();

    // Comment this out if you don't want to run the tests.
    run_tests();

})();
