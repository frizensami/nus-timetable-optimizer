 /* eslint-disable no-restricted-globals */

import { Z3Message, MessageKind } from "./z3Protocol"
// import Z3 from "../z3/z3w.js"

let solver: any = null;


/**
 * Initializes the Z3 system and sends a mesage back when the runtime is initialized
 * */
function startZ3() {
    const ctx: any = self as any;
    // Imports all names from z3w.js (includes Z3, etc)
    ctx.importScripts(ctx.location.origin + "/z3w.js");
    // @ts-ignore
    solver = Z3({
        ENVIRONMENT: "WORKER",
        onRuntimeInitialized: onRuntimeInitialized,
        print: function(message: string) { postMessage(MessageKind.PRINT, message); },
        printErr: function(message: string) { postMessage(MessageKind.ERR, message); }
    });
}

/**
 * Send a message to the worker caller that we have initialized the Z3 system
 * */
function onRuntimeInitialized() {
    postMessage(MessageKind.INITIALIZED, "")
}

/**
 * Generic function to post a message back to the caller of this worker
 * */
function postMessage(kind: MessageKind, msg: string) {
    const ctx: any = self as any;
    let message: Z3Message = { kind: kind, msg: msg };
    ctx.postMessage(message)
}

function runZ3(input: string) {
    const INPUT_FNAME = "input.smt2";
    const args = ['-smt2', INPUT_FNAME]
    // This writes the required smtlib2 code to the emscripten virtual filesystem
    solver.FS.writeFile(INPUT_FNAME, input, { encoding: "utf8" });
    // Finally, runs the solver. The print / printErr function will be called as required
    solver.callMain(args);
}

/**
 * Main handler for all incoming messages
 * */
self.addEventListener('message', function(e) {
    const message: Z3Message = e.data;
    switch (message.kind) {
        case MessageKind.INIT:
            startZ3();
            break;
        case MessageKind.OPTIMIZE:
            console.log("Optimizing...")
            runZ3(message.msg);
            break;
        default:
            break;
    }
}, false);


// export worker self.onmessage = ({ data: { text } }) => {
//   self.postMessage({ text: text + text });
// };

// this.onmessage = e => {
//     console.log('worker.js: message received from main script', e.data)

//     // const INPUT_FNAME = "input.smt2"
//     // const INPUT = `
//     //     (declare-fun x () Int)
//     //     (declare-fun y () Int)
//     //     (declare-fun z () Int)
//     //     (assert (>= (* 2 x) (+ y z)))
//     //     (declare-fun f (Int) Int)
//     //     (declare-fun g (Int Int) Int)
//     //     (assert (< (f x) (g x x)))
//     //     (assert (> (f y) (g x x)))
//     //     (check-sat)
//     //     (get-model)
//     //     (push)
//     //     (assert (= x y))
//     //     (check-sat)
//     //     (get-model)
//     //     (check-sat)
//     //     (pop)
//     //     (exit)
//     //     `;

//     // let solver = Z3({ ENVIRONMENT: "WORKER",
//     //                   onRuntimeInitialized: this.onZ3RuntimeInitialized,
//     //                   print: this.printZ3,
//     //                   printErr: this.printZ3Err});
//     // // This creates an overall args array as ["-smtlib2", "input.smt2"]
//     // const args = ["-smtlib2", INPUT_FNAME]
//     // // This writes the required smtlib2 code to the emscripten virtual filesystem
//     // solver.FS.writeFile(INPUT_FNAME, INPUT, { encoding: "utf8" });
//     // // Finally, runs the solver. The print / printErr function will be called as required
//     // solver.callMain(args);

//     this.postmessage('hello main from webworker')
// }

// this.onZ3RuntimeInitialized = () => {
//     console.log("Z3 Runtime Initialized");
// }

// this.printZ3 = (message: string) => {
//     console.log(message);
// }

// this.printZ3Err = (message: string) => {
//     console.error(message);
// }
