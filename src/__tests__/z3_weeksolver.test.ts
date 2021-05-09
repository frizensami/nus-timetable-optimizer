import { Z3WeekSolver } from '../core/z3_weeksolver'

test('Creates 6 week solver as in manually tested case', () => {
    // Y M D H M (10:30)
    const solver = new Z3WeekSolver(6)
    solver.add_weeks([2, 4, 6], "x")
    solver.add_weeks([4, 6], "y")
    solver.add_weeks([1], "z")
    const outStr = solver.generateSmtlib2String();
    expect(outStr).toEqual(`(declare-fun weeks_to_simulate () (_ BitVec 6))
(define-fun popCount13 ((x (_ BitVec 6))) (_ BitVec 6)
(bvadd
(ite (= #b1 ((_ extract 0 0) x)) #b111111 #b000000)
(ite (= #b1 ((_ extract 1 1) x)) #b111111 #b000000)
(ite (= #b1 ((_ extract 2 2) x)) #b111111 #b000000)
(ite (= #b1 ((_ extract 3 3) x)) #b111111 #b000000)
(ite (= #b1 ((_ extract 4 4) x)) #b111111 #b000000)
(ite (= #b1 ((_ extract 5 5) x)) #b111111 #b000000)
))
(declare-fun x () (_ BitVec 6))
(assert (= x #b010101))
(assert (not (= (bvand x weeks_to_simulate) #b000000)))
(declare-fun y () (_ BitVec 6))
(assert (= y #b000101))
(assert (not (= (bvand y weeks_to_simulate) #b000000)))
(declare-fun z () (_ BitVec 6))
(assert (= z #b100000))
(assert (not (= (bvand z weeks_to_simulate) #b000000)))
(minimize weeks_to_simulate)
(check-sat)
(get-value (weeks_to_simulate))
(exit)`)
});
