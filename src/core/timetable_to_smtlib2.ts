import { Lesson, Module, GenericTimetable } from './generic_timetable'
import { Z3WeekSolver } from './z3_weeksolver'

import { flipRecord, StringIdGenerator } from '../util/utils'
import { Z3Timetable, SlotConstraint, UNASSIGNED, FREE, TOOEARLY_LATE } from './z3_timetable'
import { DAYS, DAY_IDXS, HOURS_PER_DAY, IDX_DAYS, HOURS_PER_WEEK, NUM_WEEKS } from './constants'

/**
 * Convert a generic timetable to a string representing smtlib2 code
 * After using this, can be used to interpret z3 results
 * */
export class TimetableSmtlib2Converter {
    gt: GenericTimetable;
    start_hour: number
    end_hour: number
    who_id_table: Record<string, number> // string in both cases is {module id}__{lesson type}__{lesson id}
    reverse_who_id_table: Record<number, string>
    z3tt: Z3Timetable
    weeks_to_simulate: Set<number> // Each number in here is one week to simulate

    constructor(timetable: GenericTimetable, total_half_hour_slots: number, day_start_hour: number, day_end_hour: number) {
        this.gt = timetable;
        this.start_hour = day_start_hour
        this.end_hour = day_end_hour
        this.who_id_table = {}
        this.reverse_who_id_table = {}
        this.populate_who_id_tables()

        let time_str_vals: Array<string> = Array.from(new Array(total_half_hour_slots), (_: number, i: number) => {
            const [offset, day, week] = this.z3_time_to_generic_time(i);
            const dayOfWeek = this.idx_to_day_str(day);
            const hour: number = Math.floor(offset / 2) + this.start_hour;
            const hourStr: string = hour < 10 ? "0" + hour.toString() : hour.toString();
            const minuteStr: string = offset % 2 === 0 ? "00" : "30"
            return dayOfWeek + "_" + hourStr + minuteStr + "_wk" + week.toString();
        });

        this.z3tt = new Z3Timetable(total_half_hour_slots, time_str_vals)
        this.weeks_to_simulate = new Set() // 1-indexed weeks to simulate for the timetable
    }

    /**
     * Every lesson slot (unique combination of module - lessontype - lessonid) needs to have an integer representation to
     * let the solver use integer constraints. Create the tables to transform between string and integer representations.
     *
     * */
    populate_who_id_tables() {
        this.gt.modules.forEach((mod: Module, moduleidx: number, _) => {
            Object.keys(mod.lessons).forEach((lessonType: string, lessontypeidx: number, _) => {
                const lessons_of_lessontype: Array<Lesson> = mod.lessons[lessonType];
                lessons_of_lessontype.forEach((lesson: Lesson, lessonidx: number) => {
                    const key = [mod.module_id, lessonType, lesson.lesson_id].join("__");
                    this.who_id_table[key] = (moduleidx << 20) | (lessontypeidx << 10) | lessonidx;
                });
            });
        });
        this.reverse_who_id_table = flipRecord(this.who_id_table);
        // console.log(this.who_id_table);
        // console.log(this.reverse_who_id_table);
    }

    /**
     * Generate first-stage solver string for which weeks to simulate
     * */
    generateWeekSolveSmtLib2String(): string {
        const weekSolver: Z3WeekSolver = new Z3WeekSolver(NUM_WEEKS);
        let uniqueWeeks: Set<string> = new Set();

        // Go through every lessons and generate all possible unique combinations of lesson weeks
        this.gt.modules.forEach((mod: Module) => {
            Object.keys(mod.lessons).forEach((lessonType: string) => {
                const lessons_of_lessontype: Array<Lesson> = mod.lessons[lessonType];
                lessons_of_lessontype.forEach((lesson: Lesson) => {
                    // const key = [mod.module_id, lessonType, lesson.lesson_id].join("__");
                    lesson.weeks.forEach((week: Array<number>) => {
                        const weeksJson = JSON.stringify(week)
                        uniqueWeeks.add(weeksJson);
                        console.log(weeksJson)
                    });

                });
            });
        })

        // Add each unique week list to solver to generate solve string
        const ids = new StringIdGenerator();
        uniqueWeeks.forEach((uniqueWeek: string) => {
            const uniqueWeekArr = JSON.parse(uniqueWeek)
            weekSolver.add_weeks(uniqueWeekArr, ids.next());
        })

        return weekSolver.generateSmtlib2String();

    }

    update_z3_weeksolve_output(buffer: string) {
        // General structure
        // sat\n((weeks_to_simulate #b1000000000001))\n"
        const lines = buffer.split("\n");
        if (lines[0] !== "sat") throw new Error("Not SAT for week-solve before timetable solve - unexpected error, please report")

        // Extract binary string
        const line2 = lines[1];
        // Take part after first space, and part before first ) after that
        const binstring = line2.split(" ")[1].split(")")[0]
        // Ignore "#b" in string
        const binary = binstring.substring(2)
        // Create list of weeks that we should simulate
        binary.split('').forEach((c: any, idx: number) => { if (c === '1') this.weeks_to_simulate.add(idx + 1); });
        console.log("WEEKS TO SIMULATE " + Array.from(this.weeks_to_simulate).join(','))
    }

    generateTimetableSolveSmtLib2String(randomize: boolean = true): string {
        // Add all the time constraints from each module
        this.gt.modules.forEach((mod: Module) => {
            Object.keys(mod.lessons).forEach((lessonType: string) => {
                const lessons_of_lessontype: Array<Lesson> = mod.lessons[lessonType];
                const slot_constraints: Array<SlotConstraint> = this.module_lessons_to_slotconstraints(mod, lessons_of_lessontype);
                if (mod.is_compulsory) {
                    this.z3tt.add_constraints_fulfil_only_one(slot_constraints);
                } else {
                    // Make these slot constraints depend on this module ID (creates a boolean selector based on the mod id)
                    this.z3tt.add_constraints_fulfil_only_one(slot_constraints, mod.module_id);
                }
            });


        })

        // Workload constraints
        if (this.gt.constraints.workloadActive) {
            // Non-compulsory modules make up the if-then-else
            const optional_workloads: Array<[string, number]> = this.gt.modules
                .filter((mod: Module) => !mod.is_compulsory)
                .map((mod: Module) => [mod.module_id, mod.workload])
            // Compulsory modules make up the baseline workload
            const compulsory_workload_sum: number = this.gt.modules
                .filter((mod: Module) => mod.is_compulsory)
                .map((mod: Module) => mod.workload)
                .reduce((a, n) => a + Number(n), 0)
            console.log(compulsory_workload_sum)
            // Indicate that each boolean selector from the loop above has a cost if chosen
            this.z3tt.set_boolean_selector_costs(optional_workloads, compulsory_workload_sum, this.gt.constraints.minWorkload, this.gt.constraints.maxWorkload)
        }


        // Add requirements for free day: this ensures that we won't get SAT unless an entire day is free
        if (this.gt.constraints.freeDayActive || this.gt.constraints.specificFreeDaysActive) {
            const slot_constraints: Array<SlotConstraint> = this.generate_free_day_slotconstraints();
            if (this.gt.constraints.freeDayActive) {
                // We fulfil K out of N possible free days based on user selection
                // this.z3tt.add_constraints_fulfil_only_one(slot_constraints);
                this.z3tt.add_constraints_fulfil_exactly_N(slot_constraints, this.gt.constraints.numRequiredFreeDays);
            }
            if (this.gt.constraints.specificFreeDaysActive) {
                // We ensure that the days specified are free
                // Assume that the free day slot constraints are in order of day-of-week
                this.gt.constraints.specificFreeDays.forEach((freeday: string) => {
                    const day_idx = this.day_str_to_idx(freeday);
                    const day_freeday_constraints = slot_constraints[day_idx];
                    this.z3tt.add_constraints_fulfil_only_one([day_freeday_constraints]);
                })
                
            }
        }

        // Start / end too late in the day constraint
        if (this.gt.constraints.timeConstraintActive) {
            const slot_constraint: SlotConstraint | undefined = this.generate_timeconstraint_slotconstraint();
            if (slot_constraint !== undefined) {
                // MUST fulfil the single slot constraint generated for the start too early / end too late
                this.z3tt.add_constraints_fulfil_only_one([slot_constraint]);
            }
        }
        const smtlib2Str = this.z3tt.generateSmtlib2String(randomize);
        return smtlib2Str;
    }




    /**
     * Takes all lessons of a particular type from the module and converts it into a set of slot constraints,
     *  where only one of them need to be fulfilled
     * */
    module_lessons_to_slotconstraints(mod: Module, lessons: Array<Lesson>): Array<SlotConstraint> {
        let scs: Array<SlotConstraint> = [];

        lessons.forEach((lesson) => {
            const key = [mod.module_id, lesson.lesson_type, lesson.lesson_id].join("__");
            const who_id = this.who_id_table[key]
            let start_end_times: Array<[number, number]> = []
            // A lesson can have multiple start_end_times (e.g., lecture classNo 01 on Monday and Friday)
            lesson.start_end_times.forEach(([g_start_time, g_end_time], idx) => {
                // If no week calculation, run everything as every week
                if (this.weeks_to_simulate.size === 0) {
                    const start_time = this.generic_time_to_z3_time(g_start_time, lesson.days[idx]);
                    const end_time = this.generic_time_to_z3_time(g_end_time, lesson.days[idx]);
                    start_end_times.push([start_time, end_time]);
                } else {
                    // Add all start and end times for each lesson based on the weeks of this lesson that need to be simulated
                    const weeks_for_lesson = lesson.weeks[idx]
                    const weeks_to_sim = weeks_for_lesson.filter((week: number) => this.weeks_to_simulate.has(week));
                    for (let week of weeks_to_sim) {
                        console.log("Simulating week " + week)
                        const start_time = this.generic_time_to_z3_time(g_start_time, lesson.days[idx], week - 1);
                        const end_time = this.generic_time_to_z3_time(g_end_time, lesson.days[idx], week - 1);
                        start_end_times.push([start_time, end_time]);
                    }
                }

            })
            const sc: SlotConstraint = { start_end_times: start_end_times, who_id: who_id, who_id_string: key };
            scs.push(sc)
        })
        console.log(scs)
        return scs;
    }

    /**
     * Generates an entire set of slot constraints where the solver is asked to pick exactly 1
     * This ensures that at least 1 day is free.
     * NOTE: this method cares about the start-end of day timeconstraints, and will not generate variables for those slots.
     *       Otherwise, we will get UNSAT when we assert that those times are both free_day slots and too_early / too_late slots
     * */
    generate_free_day_slotconstraints(): Array<SlotConstraint> {
        let scs: Array<SlotConstraint> = [];
        // For each day of the week, add a slot constraint blocking out the whole day
        // Free Saturday is too easy, remove it
        for (let day = 0; day < DAYS - 1; day++) {
            const name = "FREE_" + this.idx_to_day_str(day); // Timeslots for this day will be named FREE_monday for e.g,
            const who_id = FREE - day; // FREE == -2, so we generate a separate who_id for each day by subtracting

            // To display the results in the table we need to map the who_id and reverse tables
            this.who_id_table[name] = who_id;
            this.reverse_who_id_table[who_id] = name;

            let startOffset = 0;
            let endOffset = (HOURS_PER_DAY * 2);
            if (this.gt.constraints.timeConstraintActive) {
                startOffset = this.hhmm_to_offset(this.gt.constraints.startTime);
                endOffset = this.hhmm_to_offset(this.gt.constraints.endTime);
                console.log(`Start offset: ${startOffset}, endOffset: ${endOffset}`)
            }

            let start_end_idxs: Array<[number, number]> = []
            for (let week of Array.from(this.weeks_to_simulate)) {
                // Generate the slot constraints for each day
                const startidx = ((week - 1) * (HOURS_PER_WEEK * 2)) + (day * (HOURS_PER_DAY * 2)) + startOffset;
                const endidx = startidx + (endOffset - startOffset);
                start_end_idxs.push([startidx, endidx])
            }

            const sc: SlotConstraint = { start_end_times: start_end_idxs, who_id: who_id, who_id_string: name }
            scs.push(sc)
        }
        return scs;
    }

    /**
     * Generates a single slot constraint representing time blocked off for too-early / too-late in the day for classes.
     * */
    generate_timeconstraint_slotconstraint(): SlotConstraint | undefined {
        let start_end_times: Array<[number, number]> = []
        const name = "TOO_EARLY_OR_LATE";
        const who_id = TOOEARLY_LATE;
        this.who_id_table[name] = who_id;
        this.reverse_who_id_table[who_id] = name;


        // Not even constraining any of the day, ignore
        const startOffset = this.hhmm_to_offset(this.gt.constraints.startTime);
        const endOffset = this.hhmm_to_offset(this.gt.constraints.endTime);
        if (startOffset === 0 && (endOffset - startOffset) === HOURS_PER_DAY * 2) return undefined;

        // For each day of the week, add a slot constraint blocking out hours before and after our ideal timings
        for (let day = 0; day < DAYS; day++) {
            // Compute the two time windows necessary to block off start and end of day
            // Start-of-day time starts at the initial index of the day, up until the offset
            // Do this for every week that we have to simulate
            for (let week of Array.from(this.weeks_to_simulate)) {
                const startidx = ((week - 1) * (HOURS_PER_WEEK * 2)) + (day * (HOURS_PER_DAY * 2));
                const startidx_endidx = startidx + startOffset;
                if (startidx_endidx - startidx > 0) {
                    start_end_times.push([startidx, startidx_endidx]);
                }

                const endidx = startidx + HOURS_PER_DAY * 2;
                const endidx_startidx = startidx + endOffset;
                if (endidx_startidx - endidx > 0) {
                    start_end_times.push([startidx, startidx_endidx]);
                }
                start_end_times.push([endidx_startidx, endidx]);
            }
        }

        const sc: SlotConstraint = { start_end_times: start_end_times, who_id: who_id, who_id_string: name }
        console.log("Slotconstraints for timeconstraint")
        console.log(sc);
        return sc;
    }


    /**
     * Converts hour and minute + day of week into an integer representing a half-hour slot in the z3 timetable
     * If the lesson is on a particular week, offset the time by (week * number of hours per week)
     * */
    generic_time_to_z3_time(timeval: Date, day: string, week: number = 0): number {
        const hour = timeval.getHours();
        const half_hour_addon = timeval.getMinutes() === 30 ? 1 : 0;
        // We assume lessons within start to end hour each day
        if (hour < this.start_hour || hour > this.end_hour) {
            throw new Error(`Lesson either starts before start_hour ${hour} < ${this.start_hour} or ends after end_hour ${hour} > ${this.end_hour}`);
        } else {
            const hour_index = hour - this.start_hour
            const day_index = this.day_str_to_idx(day)
            // hour_index * 2 (since we count half-hours)
            // + half_hour_addon since we offset by 1 unit if it's a half hour
            // + number of hours in a day * 2 to get number of half-hours
            // + number of weeks offset from the "base week" 
            const idx = (
                (hour_index * 2)
                + half_hour_addon
                + day_index * (HOURS_PER_DAY * 2)
                + week * (HOURS_PER_WEEK * 2)
            )
            return idx;
        }
    }

    /**
     * Converts a HHMM string into an integer representing a half-hour slot in the z3 timetable
     * Assumes that day is monday to get the integer offset in that day
     * */
    hhmm_to_offset(hhmm: string, week: number = 0): number {
        const hour = parseInt(hhmm.substring(0, 2))
        const half_hour_addon = parseInt(hhmm.substring(2, 4)) == 30 ? 1 : 0;
        // We assume lessons within start to end hour each day
        if (hour < this.start_hour || hour > this.end_hour) {
            throw new Error(`Lesson either starts before start_hour ${hour} < ${this.start_hour} or ends after end_hour ${hour} > ${this.end_hour}`);
        } else {
            const hour_index = hour - this.start_hour
            const day_index = 0
            const idx = (
                (hour_index * 2)
                + half_hour_addon
                + day_index * (HOURS_PER_DAY * 2)
                + week * (HOURS_PER_WEEK * 2)
            )
            return idx;
        }
    }

    /*
      Conversion from times like 0 --> (1, 0) (1st slot of the day 0-indexed, Monday)
    */
    z3_time_to_generic_time(z3_time: number): [number, number, number] {
        // Day is easy: each day has(self.end_hour - self.start_hour) * 2) slots

        // If there are 60 slots per week, and we are at slot 70, we're 10 slots into the current week
        const week = Math.floor(z3_time / (HOURS_PER_WEEK * 2))
        let z3_time_week = z3_time % (HOURS_PER_WEEK * 2)
        const day = Math.floor(z3_time_week / (HOURS_PER_DAY * 2))
        const offset = z3_time_week % (HOURS_PER_DAY * 2)
        return [offset, day, week]
    }

    /**
     * Simple conversion of string into a monday-index-0 number
     * */
    day_str_to_idx(day: string): number {
        return DAY_IDXS[day.toLowerCase()];
    }

    /**
     * Simple conversion of string into a monday-index-0 number
     * */
    idx_to_day_str(idx: number): string {
        return IDX_DAYS[idx];
    }


    /**
     * Convert the string output by the Z3 solver into a timetable-like output
     * */
    z3_output_to_timetable(z3_output: string): TimetableOutput {
        const parse = require("sexpr-plus").parse;
        const parsed_expr = parse(z3_output)
        // console.log(parsed_expr)
        const is_sat = parsed_expr[0].content === "sat"; // parsed_expr[0] === {type: "atom", content: "sat", location: {…}}
        if (!is_sat) return { is_sat: false, tt: [] }; // Nothing to do here

        let variable_assignments_exprs = parsed_expr[1].content; // parsed_expr[1] === {type: "list", content: Array(19), location: {…}}
        variable_assignments_exprs.shift(); // Removes first "model" expr: {type: "atom", content: "model", location: {…}}
        let variable_assignments: Record<string, number> = {};
        variable_assignments_exprs.forEach((expr: any) => {
            // Example expr: {type: "list", content: Array(5), location: {…}}
            // Inside Array(5):
            /*  0: {type: "atom", content: "define-fun", location: {…}}
                1: {type: "atom", content: "h33", location: {…}}
                2: {type: "list", content: Array(0), location: {…}}
                3: {type: "atom", content: "Int", location: {…}}
                4: {type: "atom", content: "1024", location: {…}}
            */
            // We assume all model returns values have this structure, and are assigning varnames to ints
            const var_name: string = expr.content[1].content
            const var_value_expr: any = expr.content[4].content
            let var_value: number = -2;
            // Var_value could be an integer or an expression where the second element is the value of a negative number
            // console.log(var_value_expr)
            if (typeof var_value_expr === "string") {
                var_value = parseInt(var_value_expr)
            } else {
                var_value = -1 * parseInt(var_value_expr[1].content)
            }

            variable_assignments[var_name] = var_value;
        })
        console.log(variable_assignments);


        // 3D array of days x hours per day x mods in that hour
        let tt = new Array(DAYS);
        for (let i = 0; i < tt.length; i++) {
            tt[i] = new Array(HOURS_PER_DAY * 2);
            for (let j = 0; j < tt[i].length; j++) {
                tt[i][j] = [];
            }
        }

        // Create the final output timetable based on hour assignments
        Object.keys(variable_assignments).forEach((key: string) => {
            // Hour assignment
            if (key.startsWith('t')) {
                const key_split = key.split("_")[0];
                const halfhouridx = parseInt(key_split.substr(1));
                const [offset, day, week] = this.z3_time_to_generic_time(halfhouridx)
                const val = variable_assignments[key];
                if (val === UNASSIGNED) return; // Un-assigned slot
                const assignment: string = this.reverse_who_id_table[val]
                if (assignment === undefined) {
                    return;
                    // throw new Error(`Undefined assignment for variable_assignments[${key}] = ${variable_assignments[key]}`)
                }
                console.log(`For z3 t${halfhouridx}, offset: ${offset}, day: ${day}, week: ${week}`)
                const modname = assignment.split("__").join("\n")
                if (!tt[day][offset].includes(modname)) {
                    tt[day][offset].push(modname);
                }

            }
        })

        console.log(tt);

        const output: TimetableOutput = {
            is_sat: is_sat,
            tt: tt
        }
        return output

    }


}

export interface TimetableOutput {
    is_sat: boolean,
    tt: Array<Array<string>>
}
