import { groupBy } from '../util/utils'

export enum LessonWeek {
    ALL = "ALL",
    EVEN = "EVEN",
    ODD = "ODD",
}

/**
 *  Specification for each Lesson:
 * - For each UNIQUE lesson_type, the timetable must contain one lesson ID of this type
 * - lesson start and end times are in 24H format, e.g., 0800, 1600, 1830
 *
 * For any Dates, we ignore everything except the hour and minute.
 * We rely on the "days" parameter to tell us which day of the week it is.
 **/
export class Lesson {
    lesson_id: string;
    lesson_type: string;
    start_end_times: Array<[Date, Date]>;
    days: Array<string>;
    weeks: LessonWeek;

    constructor(lesson_id: string, lesson_type: string, start_end_times: Array<[Date, Date]>, days: Array<string>, weeks: LessonWeek) {
        this.lesson_id = lesson_id
        this.lesson_type = lesson_type
        this.start_end_times = start_end_times
        this.days = days
        this.weeks = weeks
    }
}

/**
 * Consists of multiple lessons.
 * - Separate by types
 * - We require that all Lessons have a unique combination of <lesson_id, lesson_type>
 * - Use process_lessons() to ensure this
 * */
export class Module {
    module_id: string;
    workload: number;
    lessons: Record<string, Array<Lesson>>;
    is_compulsory: boolean;

    constructor(module_id: string, workload: number, in_lessons: Array<Lesson>, is_compulsory: boolean) {
        this.module_id = module_id
        this.workload = workload
        this.lessons = this.process_lessons(in_lessons)
        this.is_compulsory = is_compulsory
    }

    /**
     * Split all lessons up into their individual lesson types.
    *  If there is more than 1 lesson of a given type with the same number, merge them
     * */
    process_lessons(in_lessons: Array<Lesson>): Record<string, Array<Lesson>>  {

        // Split on lesson type
        // Each grouping contains lessons of  same lesson type
        let lessons_for_timetable: Record<string, Array<Lesson>> = {};

        // Iterate through each lesson type
        const grouped_lessontypes = groupBy(in_lessons, (v: Lesson) => v.lesson_type);
        grouped_lessontypes.forEach((lessons_for_lessontype, lessontype, _) => {
            lessons_for_timetable[lessontype] = [];
            // Iterate through each lesson number in that type
            const grouped_lesson_nums = groupBy(lessons_for_lessontype, (v: Lesson) => v.lesson_id)
            grouped_lesson_nums.forEach((lessons_for_lessonnum: Array<Lesson>, _lessonNum, _) => {
                if (lessons_for_lessonnum.length === 1) {
                    // If only one lesson number of this type, leave it alone
                    lessons_for_timetable[lessontype].push(lessons_for_lessonnum[0])
                } else {
                    // Otherwise, we have to merge lessons
                    const l = this.merge_lessons_same_id(lessons_for_lessonnum);
                    lessons_for_timetable[lessontype].push(l)
                }
            });
        });

        return lessons_for_timetable
    }

    merge_lessons_same_id(lessons: Array<Lesson>): Lesson {
        let start_ends = []
        let days = []
        for (const lesson of lessons) {
            start_ends.push(...lesson.start_end_times)
            days.push(...lesson.days)
        }
        const l = new Lesson(
            lessons[0].lesson_id,
            lessons[0].lesson_type,
            start_ends,
            days,
            lessons[0].weeks,
        )
        return l
    }

}

/**
 *   Intelligible interface between frontends and something that can be interpreted into a Z3Timetable.
 *
 *   Object that represents
 *   - Modules and their associated lessons and workload
 *   - An indication of which modules are required vs optional
 *   - Min and Max workload
 * 
 * */
export class GenericTimetable {
    modules: Array<Module>;
    min_workload: number;
    max_workload: number;

    constructor(modules: Array<Module>, min_workload: number, max_workload: number) {
        this.modules = modules
        this.min_workload = min_workload
        this.max_workload = max_workload
    }
}
