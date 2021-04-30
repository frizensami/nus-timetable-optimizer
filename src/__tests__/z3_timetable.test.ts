
import { Z3Timetable, SlotConstraint } from '../core/z3_timetable'

test('Z3Timetable constructs initial time arrays list as expected', () => {
    const z3tt = new Z3Timetable(4);
    expect(z3tt.timevars).toEqual(["h0", "h1", "h2", "h3"])
})

test('Z3Timetable generates expected smtlib2 hard constraints for short example', () => {
    const z3tt = new Z3Timetable(4);
    const sc: SlotConstraint = {start_end_times: [[0, 1]], who_id: 7} // ID 7 assigned to slots 0 and 1
    z3tt.add_hard_constraint(sc);
    const z3ttStr = `(declare-fun h0 () Int)
(assert-soft (= h0 -1) :weight 1 :id defaultval)
(assert (= h0 7))
(check-sat)
(get-model)
(exit)`;
    expect(z3tt.generateSmtlib2String()).toEqual(z3ttStr)
})

test('Z3Timetable generates expected smtlib2 choose-one constraints short example', () => {
    const z3tt = new Z3Timetable(4);
    const sc: SlotConstraint = {start_end_times: [[0, 1]], who_id: 7} // ID 7 assigned to slots 0 and 1
    const sc2: SlotConstraint = {start_end_times: [[2, 3]], who_id: 8} // ID 8 assigned to slots 2 and 3
    z3tt.add_constraints_fulfil_only_one([sc, sc2]);
    const z3ttExpected = `(declare-fun SL_7_8 () Int)
(assert-soft (= SL_7_8 -1) :weight 1 :id defaultval)
(declare-fun h0 () Int)
(assert-soft (= h0 -1) :weight 1 :id defaultval)
(declare-fun h2 () Int)
(assert-soft (= h2 -1) :weight 1 :id defaultval)
(assert (or (= SL_7_8 7) (= SL_7_8 8)))
(assert (= (= SL_7_8 7) (= h0 7)))
(assert (= (= SL_7_8 8) (= h2 8)))
(check-sat)
(get-model)
(exit)`;
    const z3ttReal = z3tt.generateSmtlib2String()
    // console.log(z3ttReal)
    expect(z3ttReal).toEqual(z3ttExpected)
})
