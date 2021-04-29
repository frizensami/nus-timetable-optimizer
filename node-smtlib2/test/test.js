import assert from 'assert';
import * as smt from '../lib/index';

function test1() {
    let solver = new smt.LocalCVC4Solver('QF_ALL_SUPPORTED');
    solver.add(smt.DeclareFun('x', [], 'Bool'));
    solver.add(smt.DeclareFun('y', [], 'Bool'));
    solver.assert(smt.And(smt.Or('x', 'y'), smt.Not('x'), smt.Not('y')));
    return solver.checkSat().then(([sat, assignment]) => assert(!sat)).catch((e) => {
        console.error('FAILED: ' + e.message);
    });
}
function test2() {
    let solver = new smt.LocalCVC4Solver('QF_ALL_SUPPORTED');
    solver.enableAssignments();
    solver.add(smt.DeclareFun('x', [], 'Bool'));
    solver.add(smt.DeclareFun('y', [], 'Bool'));
    solver.assert(smt.And(smt.Or('x', 'y'), 'x', 'y'));
    return solver.checkSat().then(([sat, assignment]) => {
        assert(sat);
        assert(assignment.x);
        assert(assignment.y);
    }).catch((e) => {
        console.error('FAILED: ' + e.message);
    });
}
function test3() {
    let solver = new smt.LocalCVC4Solver('QF_ALL_SUPPORTED');
    solver.enableAssignments();
    solver.add(smt.DeclareDatatype('MyType', ['C1', 'C2']));
    solver.add(smt.DeclareFun('x', [], 'Bool'));
    solver.add(smt.DeclareFun('y', [], 'Bool'));
    solver.add(smt.DeclareFun('z', [], 'MyType'));
    solver.assert(smt.And(smt.Or('x', 'y'), 'x', 'y'));
    return solver.checkSat().then(([sat, assignment]) => {
        assert(sat);
        assert(assignment.x);
        assert(assignment.y);
    }).catch((e) => {
        console.error('FAILED: ' + e.message);
    });
}
function main() {
    test1().then(() => test2()).then(() => test3());
}
main();
