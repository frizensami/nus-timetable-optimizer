const smt = require('smtlib');

export const UNASSIGNED: number = -1;
export const FREE: number = -2;
export const TOOEARLY_LATE: number = -20;
export const VAR_UNASSIGNED_WEIGHT: number = 1;
export const BOOLVAR_ASSIGNED_WEIGHT: number = 100000;

/**
 * Represents the constraints for a timetable in Z3
 * Very abstract, just deals in hour indices and integer constraints
 * */
export class Z3Timetable {
    timevars: Array<string> // ["t0", "t1", ....]
    assigned_intvars_possiblevalues: Record<string, Set<number>> // What allowed values can each time val
    bool_selectors_set: Set<string> // Basically module names e.g, CS3203, to select or de-select a module
    variables_solver: any // Just for variables assignment - hack to get the variables assignment ABOVE the constraints
    solver: any // For the actual constraints

    constructor(total_time_units: number, time_unit_names?: Array<string>) {
        // Create time variable names based on just the raw time unit, or pass in a list of strings to be appended to the raw time hours
        if (time_unit_names !== undefined) {
            if (time_unit_names.length !== total_time_units) {
                throw new Error("Size of time_unit_names array must be equal to total_time_units!");
            } else {
                this.timevars = Array.from(new Array(total_time_units), (_: number, i: number) => "t" + i + "_" + time_unit_names[i]);
            }
        } else {
            this.timevars = Array.from(new Array(total_time_units), (_: number, i: number) => "t" + i)
        }
        this.assigned_intvars_possiblevalues = {};
        this.bool_selectors_set = new Set();
        this.variables_solver = new smt.BaseSolver('QF_ALL_SUPPORTED');
        this.solver = new smt.BaseSolver('QF_ALL_SUPPORTED');
    }

    /**
     *  Indicate that a block of time cannot be used for anything else.
     *  Set all time values in the range to a fixed ID.
     * */
    // add_hard_constraint(slot: SlotConstraint) {
    //     slot.start_end_times.forEach(([start_time, end_time], _) => {
    //         for (let i = start_time; i < end_time; i++) {
    //             const timevar = this.timevars[i];
    //             // Constraint this slot
    //             this.solver.assert(smt.Eq(timevar, slot.who_id));
    //             // Add the var we just assigned to the set so that we can generate the types / constraints later
    //             this.assigned_vars_set.add(timevar);
    //         }
    //     });
    // }

    /**
     *  Add a list of constraint options, exactly one of which has to be satisfied.
        We create the slot constraints for each (AND of all non-free timeslots now).
        To ensure that only one SlotConstraint is selected, we need to create a new variable that represent this selection:

        v1: (SL78 = 7 or SL78 = 8) and (SL78 = 7 => (.. slot constraints for id 7 ..)) ...

        v2: v1 Doesn't work since due to the single-direction implication, solver can assign all the RHS without triggering LHS selector
        v2: (SL78 = 7 or SL78 = 8) and (SL78 = 7 <=> (.. slot constraints for id 7 ..)) ... [DOUBLE IMPLICATION]

        v3: v2 Doesn't work since the solver just sets one of the hour values to a random number to avoid triggering the LHS condition
        v3: v2 + add a soft constraint to all assigned variables, soft-prefer them to be marked as UNASSIGNED

        v4: Give the constraint selectors user friendly names

        v5: We need three things for us to assign a selector to ONLY one set of time constraints uniquely
            1) Assert for EACH hour-val combo, that (selector == val) == (hour == val)
                - Implication 1: If ANY of those values in that hour block are == val, then the selector is == val
                - Implication 2: if the selector is == val, then ALL those hours must be == val
            2) Set a constraint on each hour slot such that it can only take a value that could feasibly be there due to a real timeslot
                - Otherwise, the solver just puts some random number there, which can be another slot value, or even unassigned
     *
     * */
    add_constraints_fulfil_only_one(slots: Array<SlotConstraint>, boolean_selector?: string, chain_constraints: boolean = false) {
        // If we are selecting between who_ids 0, 1024, and 2048, the selector variable will be named SL_0_1024_2048
        const selector_var: string = "SL_" + slots.map((slot) => slot.who_id_string).join("_")

        // Indicate that we need to declare this later as an unconstrained variable (but we constrain it here instead)
        this.add_possible_values_to_variable(selector_var)

        // Create a list of constraints for the possible values the selector can take
        // With same example, we have SL_0_1024_2048 == 0 OR SL_0_1024_2048 == 1024 OR SL_0_1024_2048 == 2048
        let selector_var_possible_values = slots.map((slot) => smt.Eq(selector_var, slot.who_id));

        // We indicate with the boolean selector that options are selected ONLY IF the boolean selector is true
        if (boolean_selector !== undefined) {
            let selector = "OPT_" + boolean_selector; // Ensure we have an OPT prefix to indicate an optional mod
            this.bool_selectors_set.add(selector); // Make sure we declare the selector later
            // Asserts that IF the boolean selector is true, then all the possible values it can take must have at least 1 true (functionally only 1)
            this.solver.assert(smt.Eq(selector, smt.Or(...selector_var_possible_values)));
        } else {
            // Asserts unconditionally that the selector must take one of the possible values
            this.solver.assert(smt.Or(...selector_var_possible_values));
        }

        // Now, for each slot, create a double implication (equality) between the selector value and each of the constrained hours
        const constraints: Array<any> = slots.map((slot) => {
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
                    this.add_possible_values_to_variable(timevar, [slot.who_id, UNASSIGNED]);
                    // For this seletion, constraint the timevar to the who_id requested\
                    // Assert individually that if a selector is selector, that hour must be selected to it, and vice versa
                    slot_requirements.push(smt.Eq(
                        smt.Eq(selector_var, slot.who_id),
                        smt.Eq(timevar, slot.who_id)));

                }
            });
            return slot_requirements;
        }).flat(); // Flatten in case we return multiple constraints per slot

        // Decide what to do with the constraint
        if (chain_constraints) {
            // If chaining, return and let caller decide
            return constraints;
        } else {
            // If not chaining, assert them all now
            constraints.forEach((constraint: any) => this.solver.assert(constraint));
        }

    }


    /**
     * Use Z3's PbEq / PbLe / PbGe (pseudo-boolean equal / less-than / greater-than) functional to assert that a certain
     * set of constraints must remain true.
     *
     * Each slotconstraint has multiple start/end times, so many hours must be asserted to be true for a slot constraint to be true.
     * ((_ pbeq 2 1 1 1) a b c) --> pseudo-boolean equals: weight a, b, and c as 1, 1 and 1, and make sure total weight == 2 (choose 2 out of 3)
     *
     * Technique: create a selector for each set of slots, e.g., to constraint t0 = 1, t1 = 1, vs t0 = 2, t1 = 2, do:
     *  SL_somename == (t0 = 1)
     *  SL_somename == (t1 = 1)
     *
     *  SL_somename2 == (t0 = 2)
     *  SL_somename2 == (t1 = 2)
     *
     *  Then:
     *  ((_ pbeq N 1 1) SL_somename SL_somename2)
     * */
    add_constraints_fulfil_exactly_N(slots: Array<SlotConstraint>, n: number) {
        let selector_var_list: Array<string> = [];

        // Now, for each slot, create a double implication (equality) between the selector value and each of the constrained hours
        const constraints: Array<any> = slots.map((slot) => {
            // Holds all the constraints, assuming this slotconstraint is selected
            let slot_requirements: Array<any> = [];
            // Create a selector variable for this (SLKB = Selector for K-out-of-N, boolean)
            const selector_var: string = "SLKB_" + slot.who_id_string;
            selector_var_list.push(selector_var)
            slot.start_end_times.forEach(([start_time, end_time]) => {
                // Create a constraint to be "who_id" for all the start and end times in the slot constraint
                // If we said: for this slot, time slots h1 and h2 need to be = ID 1024, then
                // h1 == 1024
                // h2 == 1024
                for (let i = start_time; i < end_time; i++) {
                    const timevar = this.timevars[i];
                    // Make sure we declare this timevar since we use it
                    this.add_possible_values_to_variable(timevar, [slot.who_id, UNASSIGNED]);
                    // For this seletion, constraint the timevar to the who_id requested\
                    // Assert individually that if the boolean selector is true (selected), that hour must be selected to it, and vice versa
                    slot_requirements.push(smt.Eq(
                        selector_var,
                        smt.Eq(timevar, slot.who_id)));

                }
            });
            return slot_requirements;
        }).flat(); // Flatten in case we return multiple constraints per slot
        
        // Ensures we declare the selector later
        selector_var_list.forEach((selector: string) => this.bool_selectors_set.add(selector));

        // Assert all the constraints that relate the selector variable to the selected constrains
        constraints.forEach((constraint: any) => this.solver.assert(constraint));
        
        // Assert a K-out-of-N constraint for the selector variables
        const k_of_n = smt.PbEq(selector_var_list, new Array(selector_var_list.length).fill(1), n)
        this.solver.assert(k_of_n);
    }

    set_boolean_selector_costs(workloads: Array<[string, number]>, base_workload: number, minWorkload: number, maxWorkload: number) {
        // Create a variable for the cost of the boolean selectors, add it to declarations list
        const workload_sum_name = "workloadsum"
        this.assigned_intvars_possiblevalues[workload_sum_name] = new Set();

        // Assert that the workload sum is the sum of the if-then-else of the boolean selectors involved
        let terms = [base_workload]
        workloads.forEach(([varname, workload]) => terms.push(smt.If("OPT_" + varname, workload, 0)));
        let sumOfTerms = smt.Sum(...terms);
        this.solver.assert(smt.Eq(workload_sum_name, sumOfTerms));

        // Assert that the workload should be >= than the minimum workload and <= the maximum workload
        this.solver.assert(smt.GEq(workload_sum_name, minWorkload))
        this.solver.assert(smt.LEq(workload_sum_name, maxWorkload))
    }

    /**
     * Creates a list of variables to declare as Ints later.
     * They can be constrained to have a certain set of values.
     * If not constrained, the set will be empty
     * */
    add_possible_values_to_variable(varname: string, values: Array<number> = []) {
        if (this.assigned_intvars_possiblevalues[varname] === undefined) {
            // Make sure we at least have the UNASSIGNED possible value for the var
            this.assigned_intvars_possiblevalues[varname] = new Set(values);
        } else {
            // No set union. have to add each val independently
            values.forEach((val: number) => this.assigned_intvars_possiblevalues[varname].add(val));
        }
    }


    /**
    * Removes the first line (QF_ALL_SUPPORTED) from the output SMTLIB2 text
    * */
    generateSmtlib2String(randomize: boolean = true): string {

        // Declare all the boolean vars
        this.bool_selectors_set.forEach((boolvar: string) => {
            this.variables_solver.add(smt.DeclareFun(boolvar, [], 'Bool'))
            // this.variables_solver.add(smt.AssertSoft(boolvar, BOOLVAR_ASSIGNED_WEIGHT, 'defaultval'));
        })

        // For each variable that we use, we need to generate an indicate that it's an integer
        // We also need to assert-soft that each variable should be UNASSIGNED if possible
        Object.keys(this.assigned_intvars_possiblevalues).forEach((varname: string) => {
            // Declare variable
            this.variables_solver.add(smt.DeclareFun(varname, [], 'Int'))

            // Constrain the possible values of the var if the set is nonempty
            const var_values: Set<number> = this.assigned_intvars_possiblevalues[varname];
            if (var_values.size > 0) {
                // [(= t1 7) (= t1 8) (= t1 9)...]
                const possible_vals_eq = Array.from(var_values).map((val: number) => smt.Eq(varname, val));
                // Statement that var can take all these values 
                const all_possible_vals_or = smt.Or(...possible_vals_eq)
                this.solver.assert(all_possible_vals_or);
            }
            // this.variables_solver.add.smt.AssertSoft(smt.Eq(timevar, UNASSIGNED), VAR_UNASSIGNED_WEIGHT, 'defaultval'));
        })


        // Declare that we want as many modules to be selected as possible for now
        // TODO: change this to a workload thing? Maybe not, since that's just a bound
        // List of if-then-else conditions like (ite "CS3203" 1 0)
        // const ite_bools = Array.from(this.bool_selectors_set).map((boolvar: string) => smt.If(boolvar, 100000000, 0));
        // const ite_sum = smt.Sum(...ite_bools);
        // const maximize_term = smt.Maximize(ite_sum)
        // // const maximize_term = smt.GEq(ite_sum, 1);
        // if (ite_bools.length !== 0) {
        //     this.solver.add(maximize_term)
        // }


        let variablesStr = "";
        this.variables_solver.forEachStatement((stmt: string) => variablesStr += stmt + "\n");
        variablesStr = variablesStr.substring(variablesStr.indexOf("\n") + 1);

        let constraintStr = ""
        this.solver.forEachStatement((stmt: string) => constraintStr += stmt + "\n");
        constraintStr = constraintStr.substring(constraintStr.indexOf("\n") + 1);

        // Makes solver output random
        const randomInt = Math.floor(Math.random() * 100000000)
        let randomPrefix = randomize ? `(set-option :auto_config false)\n(set-option :smt.phase_selection 5)\n(set-option :smt.random-seed ${randomInt})\n` : "";
        // A random string that fixes a latent bug with pthread creation, likely because it causes the optimizer to kick in
        let fixBugStr = "(declare-fun BUGFIX_VAR_DONTASK () Int)\n(assert-soft (= BUGFIX_VAR_DONTASK 10))\n"
        // The string that executes the solver and retrives the final model and objectives
        let solveStr = "(check-sat)\n(get-model)\n(get-objectives)\n(exit)"
        // Overall SMTLIB2 string to return
        const finalStr = randomPrefix + variablesStr + constraintStr + fixBugStr + solveStr;
        console.log(finalStr);
        return finalStr;
    }

}


export interface SlotConstraint {
    start_end_times: Array<[number, number]> // Array of start and end times
    who_id: number
    who_id_string: string // string representing the who_id number as a user-interpretable string
}
