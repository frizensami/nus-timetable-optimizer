// -*- mode: typescript; indent-tabs-mode: nil; js-basic-offset: 4 -*-
//
// Copyright 2017-2020 Giovanni Campagna <gcampagn@cs.stanford.edu>
//
// See LICENSE for details

import * as child_process from 'child_process';
import byline from 'byline';

import * as smt from './smtlib';
import BaseSolver from './base_solver';

export default class LocalCVC4Solver extends BaseSolver {
    constructor(logic : string) {
        super(logic);
        this.setOption('strings-exp');
        this.setOption('strings-guess-model');
    }

    checkSat() : Promise<[boolean, Record<string,number|boolean>|undefined]> {
        return new Promise((callback, errback) => {
            this.add(smt.CheckSat());

            const args = ['--lang', 'smt2.6', '--tlimit=' + this.timeLimit, '--cpu-time'];
            if (this.withAssignments)
                args.push('--dump-models');

            const now = new Date;
            const child = child_process.spawn('cvc4', args);

            child.stdin.setDefaultEncoding('utf8');
            this.forEachStatement((stmt) => child.stdin.write(stmt.toString()));
            child.stdin.end();
            child.stderr.setEncoding('utf8');
            const stderr = byline(child.stderr);
            stderr.on('data', (data : string) => {
                console.error('SMT-ERR:', data);
            });
            child.stdout.setEncoding('utf8');
            const stdout = byline(child.stdout);
            let sat : boolean|undefined = undefined;
            const assignment : Record<string,number|boolean> = {};
            let cidx = 0;
            const constants : Record<string,number> = {};
            stdout.on('data', (line : string) => {
                //console.log('SMT:', line);
                if (line === 'sat') {
                    sat = true;
                    return;
                }
                if (line === 'unsat') {
                    sat = false;
                    return;
                }
                if (line === 'unknown') {
                    sat = true;
                    console.error('SMT TIMED OUT');
                    this.dump();
                    return;
                }
                if (line.startsWith('(error')) {
                    errback(new Error('SMT error: ' + line));
                    return;
                }

                const CONSTANT_REGEX = /; rep: @uc_([A-Za-z0-9_]+)$/;
                let match = CONSTANT_REGEX.exec(line);
                if (match !== null) {
                    constants[match[1]] = cidx++;
                    return;
                }
                const ASSIGN_CONST_REGEX = /\(define-fun ([A-Za-z0-9_.]+) \(\) ([A-Za-z0-9_]+) @uc_([A-Za-z0-9_]+)\)$/;
                match = ASSIGN_CONST_REGEX.exec(line);
                if (match !== null) {
                    assignment[match[1]] = constants[match[3]];
                    return;
                }

                const ASSIGN_BOOL_REGEX = /\(define-fun ([A-Za-z0-9_.]+) \(\) Bool (true|false)\)$/;
                match = ASSIGN_BOOL_REGEX.exec(line);
                if (match !== null)
                    assignment[match[1]] = (match[2] === 'true');

                // ignore everything else
            });
            stdout.on('end', () => {
                console.log('SMT elapsed time: ' + ((new Date).getTime() - now.getTime()));

                if (sat)
                    callback([true, assignment]);
                else
                    callback([false, undefined]);
            });

            child.stdout.on('error', errback);
        });
    }
}
