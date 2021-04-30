import { Lesson, Module, GenericTimetable } from './generic_timetable'
import { NUSModsFrontend } from '../frontends/nusmods_frontend'
import { TimetableSmtlib2Converter } from './timetable_to_smtlib2'

const DAYS = 5  // One week
const HOURS_PER_DAY = 14  // 8 am --> 10 pm
const DAY_START_HOUR = 8
const DAY_END_HOUR = 22

export async function smtTest() {
    const smt = require('smtlib');
    let nusmods_fe = new NUSModsFrontend();
    await nusmods_fe.add_module("CS3203", "2020-2021", 1, true)
    console.log(nusmods_fe);
    const gt: GenericTimetable = nusmods_fe.create_timetable(5, 10);
    const conv: TimetableSmtlib2Converter = new TimetableSmtlib2Converter(gt,
        DAYS * HOURS_PER_DAY * 2, // Number of "half-hour" slots
        DAY_START_HOUR, // Start at 8am
        DAY_END_HOUR) // End at 2200 (10 pm)
    const smtString = conv.generateSmtLib2String();
    // It's BaseSmtSolver in the code but it's exported as BaseSolver
    // let solver = new smt.BaseSolver('QF_ALL_SUPPORTED');
    // solver.add(smt.DeclareFun('x', [], 'Bool'))
    // let outStr = solverToString(solver);
    return smtString;
}

/**
 * Removes the first line (QF_ALL_SUPPORTED) from the output SMTLIB2 text
 * */
function solverToString(solver: any): string {
    let outStr = "";
    solver.forEachStatement((stmt: string) => outStr += stmt + "\n");
    const firstLineRemoved = outStr.substring(outStr.indexOf("\n") + 1);
    return firstLineRemoved;
}
