import { LessonWeek, Lesson, Module, GenericTimetable } from './generic_timetable'

import { flipRecord } from '../util/utils'
import { Z3Timetable, SlotConstraint, UNASSIGNED } from './z3_timetable'

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

    constructor(timetable: GenericTimetable, total_half_hour_slots: number, day_start_hour: number, day_end_hour: number) {
        this.gt = timetable;
        this.start_hour = day_start_hour
        this.end_hour = day_end_hour
        this.who_id_table = {}
        this.reverse_who_id_table = {}
        this.populate_who_id_tables()
        this.z3tt = new Z3Timetable(total_half_hour_slots)
    }

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

    generateSmtLib2String(): string {
        this.gt.modules.forEach((mod: Module) => {
            if (!mod.is_compulsory) {
                throw new Error("Non compulsory modules not implemented yet!"); // TODO implement
            } else {
                Object.keys(mod.lessons).forEach((lessonType: string, lessontypeidx: number, _) => {
                    const lessons_of_lessontype: Array<Lesson> = mod.lessons[lessonType];
                    const slot_constraints: Array<SlotConstraint> = this.module_lessons_to_slotconstraints(mod, lessons_of_lessontype);
                    this.z3tt.add_constraints_fulfil_only_one(slot_constraints);
                });
            }
        })
        const smtlib2Str = this.z3tt.generateSmtlib2String();
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
            lesson.start_end_times.forEach(([g_start_time, g_end_time], idx) => {
                const start_time = this.generic_time_to_z3_time(g_start_time, lesson.days[idx]);
                const end_time = this.generic_time_to_z3_time(g_end_time, lesson.days[idx]);
                start_end_times.push([start_time, end_time]);
            })
            const sc: SlotConstraint = { start_end_times: start_end_times, who_id: who_id };
            scs.push(sc)
        })
        return scs;
    }

    /**
     * Converts hour and minute + day of week into an integer representing a half-hour slot in the z3 timetable:w
     * */
    generic_time_to_z3_time(timeval: Date, day: string): number {
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
            const idx = (
                (hour_index * 2)
                + half_hour_addon
                + day_index * ((this.end_hour - this.start_hour) * 2)
            )
            return idx;
        }
    }

    /*
      Conversion from times like 0 --> (1, 0) (1st slot of the day 0-indexed, Monday)
    */
    z3_time_to_generic_time(z3_time: number): [number, number] {
        // Day is easy: each day has(self.end_hour - self.start_hour) * 2) slots
        const day = Math.floor(z3_time / ((this.end_hour - this.start_hour) * 2))
        const offset = z3_time % ((this.end_hour - this.start_hour) * 2)
        return [offset, day]
    }

    /**
     * Simple conversion of string into a monday-index-0 number
     * */
    day_str_to_idx(day: string): number {
        const day_idxs: Record<string, number> = {
            "monday": 0,
            "tuesday": 1,
            "wednesday": 2,
            "thursday": 3,
            "friday": 4,
        }
        return day_idxs[day.toLowerCase()];
    }


    /**
     * Convert the string output by the Z3 solver into a timetable-like output
     * */
    z3_output_to_timetable(z3_output: string): TimetableOutput {
        const parse = require("sexpr-plus").parse;
        const parsed_expr = parse(z3_output)
        console.log(parsed_expr)
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
            console.log(var_value_expr)
            if (typeof var_value_expr === "string") {
                var_value = parseInt(var_value_expr)
            } else {
                var_value = -1 * parseInt(var_value_expr[1].content)
            }

            variable_assignments[var_name] = var_value;
        })
        console.log(variable_assignments);


        // 2D array of days (assuming that doesn't change...) x half-hours per day
        let tt = new Array(5);
        for (let i = 0; i < tt.length; i++) {
            tt[i] = Array((this.end_hour - this.start_hour) * 2).fill("");
        }

        // Create the final output timetable based on hour assignments
        Object.keys(variable_assignments).forEach((key: string) => {
            // Hour assignment
            if (key.startsWith('h')) {
                const halfhouridx = parseInt(key.substr(1));
                const [offset, day] = this.z3_time_to_generic_time(halfhouridx)
                const val = variable_assignments[key];
                if (val == UNASSIGNED) return; // Un-assigned slot
                const assignment: string = this.reverse_who_id_table[val]
                if (assignment === undefined) throw new Error(`Undefined assignment for variable_assignments[${key}] = ${variable_assignments[key]}`)
                tt[day][offset] = assignment.split("__").join("\n");
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
