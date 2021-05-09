import { groupBy } from '../util/utils'

// export enum LessonWeek {
//     ALL = "ALL",
//     EVEN = "EVEN",
//     ODD = "ODD",
// }

// We can either specify that we lesson is on all / even (2,4,6,8,10) / odd weeks (1,3,5,7,9) OR we specify the weeks individually
// Since a single lesson can permit multiple timeslots, which might be spread across weeks, we need to specify this as an array
// For e.g., imagine classType 1 lesson 01 ==> lab on tuesday 10am even weeks and lab on thursday 10am odd weeks
// export type LessonWeeks = Array<LessonWeek | Array<number>>;

export interface GlobalConstraintsList {
    workloadActive: boolean,
    minWorkload: number,
    maxWorkload: number
    freeDayActive: boolean,
    startTime: string,
    endTime: string
    timeConstraintActive: boolean
}

export const defaultConstraints: GlobalConstraintsList = {
    workloadActive: false,
    minWorkload: 0,
    maxWorkload: 30,
    freeDayActive: false,
    startTime: "0800",
    endTime: "2200",
    timeConstraintActive: false,
};

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
    weeks: Array<Array<number>>; // list of weeks where lesson is active

    constructor(lesson_id: string, lesson_type: string, start_end_times: Array<[Date, Date]>, days: Array<string>, weeks: Array<Array<number>>) {
        this.lesson_id = lesson_id.replace(/\s/g, '')
        this.lesson_type = lesson_type.replace(/\s/g, '')
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
    lessons: Record<string, Array<Lesson>>; // mapping from lessonType ==> all lessons of that type
    is_compulsory: boolean;

    constructor(module_id: string, workload: number, in_lessons: Array<Lesson>, is_compulsory: boolean) {
        this.module_id = module_id.replace(/\s/g, '')
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
        let weeks = []
        for (const lesson of lessons) {
            start_ends.push(...lesson.start_end_times)
            days.push(...lesson.days)
            weeks.push(...lesson.weeks)
        }
        const l = new Lesson(
            lessons[0].lesson_id,
            lessons[0].lesson_type,
            start_ends,
            days,
            weeks,
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
    constraints: GlobalConstraintsList


    constructor(modules: Array<Module>, constraints: GlobalConstraintsList) {
        this.modules = modules
        this.constraints = constraints
    }
}
