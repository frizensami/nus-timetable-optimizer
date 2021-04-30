import { LessonWeek, Lesson, Module, GenericTimetable } from './generic_timetable'
import { flipRecord } from '../util/utils'
import { Z3Timetable, SlotConstraint } from './z3_timetable'

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
                    this.who_id_table[key] = moduleidx << 20 | lessontypeidx << 10 | lessonidx;
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
        const half_hour_addon = timeval.getMinutes() == 30 ? 1 : 0;
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


}
