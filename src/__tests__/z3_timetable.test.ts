import { Z3Timetable, SlotConstraint } from '../core/z3_timetable';

test('Z3Timetable constructs initial time arrays list as expected', () => {
    const z3tt = new Z3Timetable(4);
    expect(z3tt.timevars).toEqual(['t0', 't1', 't2', 't3']);
});

test('Z3Timetable generates expected smtlib2 choose-one constraints short example', () => {
    const z3tt = new Z3Timetable(4);
    const sc: SlotConstraint = {
        start_end_times: [[0, 1]],
        who_id: 7,
        who_id_string: '7',
    }; // ID 7 assigned to slots 0 and 1
    const sc2: SlotConstraint = {
        start_end_times: [[2, 3]],
        who_id: 8,
        who_id_string: '8',
    }; // ID 8 assigned to slots 2 and 3
    z3tt.add_constraints_fulfil_only_one([sc, sc2]);
    const z3ttExpected = `(declare-fun SL_7_8 () Int)
(declare-fun t0 () Int)
(declare-fun t2 () Int)
(assert (or (= SL_7_8 7) (= SL_7_8 8)))
(assert (= (= SL_7_8 7) (= t0 7)))
(assert (= (= SL_7_8 8) (= t2 8)))
(assert (or (= t0 7) (= t0 -1)))
(assert (or (= t2 8) (= t2 -1)))
(declare-fun BUGFIX_VAR_DONTASK () Int)
(assert-soft (= BUGFIX_VAR_DONTASK 10))
(check-sat)
(get-model)
(get-objectives)
(exit)`;
    const z3ttReal = z3tt.generateSmtlib2String(false);
    // console.log(z3ttReal)
    expect(z3ttReal).toEqual(z3ttExpected);
});
