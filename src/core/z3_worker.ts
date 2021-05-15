/* eslint-disable no-restricted-globals */

import { Z3Message, MessageKind } from './z3_protocol';
// import Z3 from "../z3/z3w.js"

let solver: any = null;

/**
 * Initializes the Z3 system and sends a mesage back when the runtime is initialized
 * */
function startZ3() {
    const ctx: any = self as any;
    // Imports all names from z3w.js (includes Z3, etc)
    ctx.importScripts(ctx.location.origin + '/z3w.js');
    // @ts-ignore
    solver = Z3({
        ENVIRONMENT: 'WORKER',
        onRuntimeInitialized: onRuntimeInitialized,
        print: function(message: string) {
            postMessage(MessageKind.PRINT, message);
        },
        printErr: function(message: string) {
            postMessage(MessageKind.ERR, message);
        },
        postRun: function() {
            postMessage(MessageKind.EXIT, '');
        },
    });
}

/**
 * Send a message to the worker caller that we have initialized the Z3 system
 * */
function onRuntimeInitialized() {
    postMessage(MessageKind.INITIALIZED, '');
}

/**
 * Generic function to post a message back to the caller of this worker
 * */
function postMessage(kind: MessageKind, msg: string) {
    const ctx: any = self as any;
    let message: Z3Message = { kind: kind, msg: msg };
    ctx.postMessage(message);
}

function runZ3(input: string) {
    const INPUT_FNAME = 'input.smt2';
    const args = ['-smt2', INPUT_FNAME];
    // This writes the required smtlib2 code to the emscripten virtual filesystem
    solver.FS.writeFile(INPUT_FNAME, input, { encoding: 'utf8' });
    // Finally, runs the solver. The print / printErr function will be called as required
    solver.callMain(args);
    // Run when the solver is done
    postMessage(MessageKind.EXIT, '');
}

/**
 * Main handler for all incoming messages
 * */
self.addEventListener(
    'message',
    function(e) {
        const message: Z3Message = e.data;
        switch (message.kind) {
            case MessageKind.INIT:
                startZ3();
                break;
            case MessageKind.OPTIMIZE:
                console.log('Optimizing...');
                runZ3(message.msg);
                break;
            default:
                break;
        }
    },
    false
);
