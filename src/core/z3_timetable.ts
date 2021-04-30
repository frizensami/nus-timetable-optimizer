const smt = require('smtlib');

export const UNASSIGNED: number = -1;

/**
 * Represents the constraints for a timetable in Z3
 * Very abstract, just deals in hour indices and integer constraints
 * */
export class Z3Timetable {
    timevars: Array<string> // ["h0", "h1", ....]
    assigned_vars_set: Set<string>
    variables_solver: any // Just for variables assignment - hack to get the variables assignment ABOVE the constraints
    solver: any // For the actual constraints

    constructor(total_time_units: number) {
        this.timevars = Array.from(new Array(total_time_units), (_: number, i: number) => "h" + i);
        this.assigned_vars_set = new Set();
        this.variables_solver = new smt.BaseSolver('QF_ALL_SUPPORTED');
        this.solver = new smt.BaseSolver('QF_ALL_SUPPORTED');
    }

    /**
     *  Indicate that a block of time cannot be used for anything else.
     *  Set all time values in the range to a fixed ID.
     * */
    add_hard_constraint(slot: SlotConstraint) {
        slot.start_end_times.forEach(([start_time, end_time], _) => {
            for (let i = start_time; i < end_time; i++) {
                const timevar = this.timevars[i];
                // Constraint this slot
                this.solver.assert(smt.Eq(timevar, slot.who_id));
                // Add the var we just assigned to the set so that we can generate the types / constraints later
                this.assigned_vars_set.add(timevar);
            }
        });
    }

    /**
     *  Add a list of constraint options, exactly one of which has to be satisfied.
        We create the slot constraints for each (AND of all non-free timeslots now).
        To ensure that only one SlotConstraint is selected, we need to create a new variable that represent this selection:

        v1: (SL78 = 7 or SL78 = 8) and (SL78 = 7 => (.. slot constraints for id 7 ..)) ...

        v2: v1 Doesn't work since due to the single-direction implication, solver can assign all the RHS without triggering LHS selector
        v2: (SL78 = 7 or SL78 = 8) and (SL78 = 7 <=> (.. slot constraints for id 7 ..)) ... [DOUBLE IMPLICATION]

        v3: v2 Doesn't work since the solver just sets one of the hour values to a random number to avoid triggering the LHS condition
        v3: v2 + add a soft constraint to all assigned variables, soft-prefer them to be marked as UNASSIGNED
     *
     * */
    add_constraints_fulfil_only_one(slots: Array<SlotConstraint>) {
        // If we are selecting between who_ids 0, 1024, and 2048, the selector variable will be named SL_0_1024_2048
        const selector_var: string = "SL_" + slots.map((slot) => slot.who_id).join("_")

        // Make sure we declare this value later to be an integer
        this.assigned_vars_set.add(selector_var)

        // Create a list of constraints for the possible values the selector can take
        // With same example, we have SL_0_1024_2048 == 0 OR SL_0_1024_2048 == 1024 OR SL_0_1024_2048 == 2048
        let selector_var_possible_values = slots.map((slot) => smt.Eq(selector_var, slot.who_id));
        this.solver.assert(smt.Or(...selector_var_possible_values));

        // Now, for each slot, create a double implication (equality) between the selector value and each of the constrained hours
        slots.forEach((slot) => {
            // Holds all the constraints, assuming this slotconstraint is selected
            let slot_requirements: Array<any> = [];
            slot.start_end_times.forEach(([start_time, end_time]) => {
                // Create a constraint to be "who_id" for all the start and end times in the slot constraint
                // If we said: for this slot, time slots h1 and h2 need to be = ID 1024, then
                // h1 == 1024
                // h2 == 1024
                for (let i = start_time; i < end_time; i++) {
                    const timevar = this.timevars[i];
                    // Make sure we declare this timevar since we use it
                    this.assigned_vars_set.add(timevar);
                    // For this seletion, constraint the timevar to the who_id requested
                    slot_requirements.push(smt.Eq(timevar, slot.who_id));
                }
            });
            // With all the requirements for the slot, add an implication that if we take a particular selector value,
            // we must pick all these slot constraints (and vice versa)
            // This is basically : (SL_0_1024_2048 == 1024) == (h1 == 1024 AND h2 == 1024)
            this.solver.assert(
                smt.Eq(
                    smt.Eq(selector_var, slot.who_id),
                    smt.And(...slot_requirements)));
        });
        
    }

    /**
    * Removes the first line (QF_ALL_SUPPORTED) from the output SMTLIB2 text
    * */
    generateSmtlib2String(): string {
        // For each variable that we use, we need to generate an indicate that it's an integer
        this.assigned_vars_set.forEach((timevar: string) => {
            this.variables_solver.add(smt.DeclareFun(timevar, [], 'Int'))
            this.variables_solver.add(smt.AssertSoft(smt.Eq(timevar, UNASSIGNED), 1, 'defaultval'));
        })
        // We also need to assert-soft that each variable should be UNASSIGNED if possible
        
        let variablesStr = "";
        this.variables_solver.forEachStatement((stmt: string) => variablesStr += stmt + "\n");
        variablesStr = variablesStr.substring(variablesStr.indexOf("\n") + 1);

        let constraintStr = ""
        this.solver.forEachStatement((stmt: string) => constraintStr += stmt + "\n");
        constraintStr = constraintStr.substring(constraintStr.indexOf("\n") + 1);

        // Final string to run the solver
        let solveStr = "(check-sat)\n(get-model)\n(exit)"
        return variablesStr + constraintStr + solveStr;
    }

}


export interface SlotConstraint {
    start_end_times: Array<[number, number]> // Array of start and end times
    who_id: number
}
