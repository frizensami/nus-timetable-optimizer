

/* eslint-disable no-restricted-globals */
self.addEventListener('message', function(e) { 
    /* eslint-disable no-restricted-globals */
    self.postMessage(e.data); 
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
