 const smt = require('smtlib');

const UNASSIGNED: number = -1;

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
     * Asserts that a number of constraints have to be fulfilled all at the same time
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
        return variablesStr + constraintStr;
    }

}


export interface SlotConstraint {
    start_end_times: Array<[number, number]> // Array of start and end times
    who_id: number
}
