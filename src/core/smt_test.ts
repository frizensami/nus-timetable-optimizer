import { Lesson, Module, GenericTimetable } from './generic_timetable'
import { NUSModsFrontend } from '../frontends/nusmods_frontend'

export function smtTest() {
    const smt = require('smtlib');
    let nusmods_fe = new NUSModsFrontend();
    nusmods_fe.add_module("CS3203", "2020-2021", 1, true).then(() => {
        console.log(nusmods_fe);
        // It's BaseSmtSolver in the code but it's exported as BaseSolver
        let solver = new smt.BaseSolver('QF_ALL_SUPPORTED');
        solver.add(smt.DeclareFun('x', [], 'Bool'))
        let outStr = solverToString(solver);
        return outStr;
    })

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
