import { LessonWeek, Lesson, Module, GenericTimetable } from './generic_timetable'
import { flipRecord } from '../util/utils'

/**
 * Convert a generic timetable to a string representing smtlib2 code
 * After using this, can be used to interpret z3 results
 * */
export class TimetableSmtlib2Converter {
    gt: GenericTimetable;
    start_hour: number
    end_hour: number
    who_id_table: Record<string, number>; // string in both cases is {module id}__{lesson type}__{lesson id}
    reverse_who_id_table: Record<number, string>;

    constructor(timetable: GenericTimetable, total_half_hour_slots: number, day_start_hour: number, day_end_hour: number) {
        this.gt = timetable;
        this.start_hour = day_start_hour
        this.end_hour = day_end_hour
        this.who_id_table = {}
        this.reverse_who_id_table = {}
        this.populate_who_id_tables()
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


}
