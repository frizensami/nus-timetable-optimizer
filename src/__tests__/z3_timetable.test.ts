
import { Z3Timetable, SlotConstraint } from '../core/z3_timetable'

test('Z3Timetable constructs initial time arrays list as expected', () => {
    const z3tt = new Z3Timetable(4);
    expect(z3tt.timevars).toEqual(["h0", "h1", "h2", "h3"])
})

test('Z3Timetable generates expected smtlib2 for constrained values for short example', () => {
    const z3tt = new Z3Timetable(4);
    const sc: SlotConstraint = {start_end_times: [[0, 1]], who_id: 7} // ID 7 assigned to slots 0 and 1
    z3tt.add_hard_constraint(sc);
    const z3ttStr = "(declare-fun h0 () Int)\n(assert-soft (= h0 -1) :weight 1 :id defaultval)\n(assert (= h0 7))\n";
    expect(z3tt.generateSmtlib2String()).toEqual(z3ttStr)
})
