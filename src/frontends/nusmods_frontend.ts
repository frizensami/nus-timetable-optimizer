import { LessonWeek, Lesson, Module, GenericTimetable, GlobalConstraintsList } from '../core/generic_timetable'
import { groupBy } from '../util/utils'
// @ts-ignore
import ExpiredStorage from 'expired-storage'

const EXPIRY_HOURS = 24;
const EXPIRY_MINUTES = EXPIRY_HOURS * 60
const EXPIRY_SECS = EXPIRY_MINUTES * 60 

export interface ModuleToAdd {
    module_code: string,
    acad_year: string,
    semester: number,
    is_compulsory: boolean
}

export class NUSModsFrontend {
    modules: Array<Module> = [];

    async add_modules(modules_to_add: Array<ModuleToAdd>) {
        for (let mod of modules_to_add) {
            await this.add_module(mod) 
        }
    }

    /**
     * Lookup a module JSON in our server and add it and its lessons to our list of modules
     * */
    async add_module({module_code, acad_year, semester, is_compulsory}: ModuleToAdd): Promise<boolean> {
        const data: any = await NUSModsFrontend.read_module_json(module_code, acad_year, semester)
        if (data === {}) return false; // No module to add - didn't fit our specifications

        const semdata = data["semesterData"].find((v: any) => v.semester === semester);
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

        return true; // Managed to add the module
    }

    /**
     * Read module data from local storage first, then nusmods API
     * */
    static async read_module_json(module_code: string, acad_year: string, semester: number): Promise<object> {
        const localjson = NUSModsFrontend.read_module_local(module_code, acad_year, semester);
        if (Object.keys(localjson).length === 0) {
            const remotejson = await NUSModsFrontend.read_module_nusmods_api(module_code, acad_year, semester);
            console.log("Retrieved module from NUSMods API, stored locally.")
            NUSModsFrontend.store_module_local(module_code, acad_year, semester, remotejson);
            return remotejson;
        } else {
            console.log("Retrieved module from localStorage!")
            return localjson;
        }
    }

    /**
     * Read module data as public json files from our server
     * */
    static async read_module_server(module_code: string, acad_year: string, semester: number): Promise<object> {
        const baseUrl = window.location.protocol + "//" + window.location.hostname + (window.location.port ? ':' + window.location.port: '');
        const finalUrl = `${baseUrl}/modules/${acad_year}/${module_code}.json`;
        // console.log(`Fetching ${finalUrl}`)
        try {
            const response = await fetch(finalUrl)
            const mod = await response.json();
            // We check if the mod exists
            const exists = mod["semesterData"].find((v: any) => v.semester === semester) !== undefined;
            // If it doesn't return an empty dict, or return the mod itself
            return exists ? mod : {};
        } catch {
            return {};
        }
    }

    /**
     * Try to retrieve module information from local storage first
     * */
    static read_module_local(module_code: string, acad_year: string, semester: number): Promise<object> {
        let expiredStorage = new ExpiredStorage();
        const key = `${module_code}__${acad_year}__${semester}`;
        const mod = expiredStorage.getJson(key)
        expiredStorage.clearExpired(); // take the chance to remove expired vals
        return (mod === undefined || mod === null) ? {} : mod;
    }

    /**
     * Try to retrieve module information from local storage first
     * */
    static store_module_local(module_code: string, acad_year: string, semester: number, json: object) {
        let expiredStorage = new ExpiredStorage();
        const key = `${module_code}__${acad_year}__${semester}`;
        expiredStorage.setJson(key, json, EXPIRY_SECS);
        
        
    }

    static async read_module_nusmods_api(module_code: string, acad_year: string, semester: number): Promise<object> {
        const baseUrl = "https://api.nusmods.com/v2"
        const finalUrl = `${baseUrl}/${acad_year}/modules/${module_code}.json`;
        // console.log(`Fetching ${finalUrl}`)
        try {
            const response = await fetch(finalUrl)
            const mod = await response.json();
            // We check if the mod exists
            const exists = mod["semesterData"].find((v: any) => v.semester === semester) !== undefined;
            // If it doesn't return an empty dict, or return the mod itself
            return exists ? mod : {};
        } catch {
            return {};
        }
    }


    /**
     * Creates a GenericTimetable from the current state
     * */
    create_timetable(constraints: GlobalConstraintsList): GenericTimetable {
        const g = new GenericTimetable(
            this.modules,
            constraints,
        )
        return g
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
