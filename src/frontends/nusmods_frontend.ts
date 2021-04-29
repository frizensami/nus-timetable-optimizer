import { LessonWeek, Lesson, Module, GenericTimetable } from '../core/generic_timetable'
import { groupBy } from '../util/utils'

export class NUSModsFrontend {
    modules: Array<Module> = [];

    /**
     * Lookup a module JSON in our server and add it and its lessons to our list of modules
     * */
    async add_module(module_code: string, acad_year: string, semester: number, is_compulsory: boolean) {
        const data: any = await this.read_module_json(module_code, acad_year)
        const semdata = data["semesterData"][semester - 1]
        const timetable = semdata["timetable"]

        // Create generic lessons
        let generic_lessons: Array<any> = []
        const grouped_lessontypes = groupBy(timetable, (v: any) => v["lessonType"]);
        grouped_lessontypes.forEach((value: Array<Lesson>, _key: string, _: any) => {
            // console.log(`m[${key}] = ${JSON.stringify(value)}`);
            const lessons_for_lessontype = value
            lessons_for_lessontype.forEach((lesson: any) => {
                const generic_lesson = this.lesson_to_genericlesson(lesson);
                generic_lessons.push(generic_lesson);
            })
        });

        // console.log("Lessons for module")
        // console.log(JSON.stringify(generic_lessons));

        // Create the overall generic module
        let m = new Module(
            data["moduleCode"],
            data["moduleCredit"],
            generic_lessons,
            is_compulsory,
        )
        this.modules.push(m)
    }

    /**
     * Read module data as public json files from our server
     * */
    async read_module_json(module_code: string, acad_year: string): Promise<object> {
        const baseUrl = window.location.protocol + "//" + window.location.hostname + (window.location.port ? ':' + window.location.port: '');
        const finalUrl = `${baseUrl}/modules/${acad_year}/${module_code}.json`;
        console.log(`Fetching ${finalUrl}`)
        const response = await fetch(finalUrl)
        const mod = await response.json();
        return mod;
    }

    /**
     * Convert a lesson from NUSMods JSON into our generic lesson format
     * */
    lesson_to_genericlesson(lesson: any) {
        const l = new Lesson(
            lesson["classNo"],
            lesson["lessonType"],
            [this.lesson_to_start_end_times(lesson)],
            [lesson["day"]],
            LessonWeek.ALL,  // TODO actually process this
        )
        return l
    }

    /**
     * Get the start and end times of a lesson (0800, 1630, etc) as Javascript date objects
     * */
    lesson_to_start_end_times(lesson: any): [Date, Date] {
        // 8am and 9am are represented as 0800 and 0900
        let start_time = lesson["startTime"]
        let end_time = lesson["endTime"]

        // Convert hhmm values like 0800 and 1630 to a date value
        function hhmm_to_date(hhmm: string) {
            const hour = parseInt(hhmm.substr(0, 2));
            const minutes = parseInt(hhmm.substr(2, 4));
            return new Date(1970, 1, 1, hour, minutes);
        }
        
        start_time = hhmm_to_date(start_time)
        end_time = hhmm_to_date(end_time)
        return [start_time, end_time]
    }
}
