# NUSMods Timetable Arranger - Web Version

## Objectives
- Allow users to arrange their NUS timetable based on their specified constraints, e.g.,
      - Keep lunch hours free
      - No classes before 9 am, etc
      - Try to get a free day
- This system should run primarily on the user's own infrastructure (i.e., in their browser) 
      - Purpose: keep server load low. Necessary due to SMT solving being CPU-heavy.

## Architecture
- **React frontend** that should call little to no APIs on the backend that serves it (i.e., backend should primarily exist just to serve the app as-is)
- Frontend should take in user timetable and constraints (keep it to an MVP-level frontend for now) and **convert those into SMTLIB2 code**
- Frontend should then **call the z3 wasm binary** that will execute the SMTLIB2 code and read + format the results


## Building and Running
- `src/z3` was downloaded from the initial release [here](https://github.com/cpitclaudel/z3.wasm/releases), since building it was error-prone

## Working with the z3.wasm project
- `z3.wasm` [here](https://github.com/cpitclaudel/z3.wasm) doesn't have a lot of documentation. We need to figure out how to call it from the examples
- `z3.wasm` basically is the command line version of z3, which takes in command line options and a file with smt2 code
- Seems like we need to pass `args`, should  be just "-smt2"
- We can extract the critical lines (spread across functions):

```javascript
/* Initializes the Z3 solver - here it assumes 
- it's running in a web worker
- it will call the runtime initialization function when ready 
- it will call the print functions specified
*/
solver = Z3({ ENVIRONMENT: "WORKER",
                      onRuntimeInitialized: onRuntimeInitialized,
                      print: function(message) { postOutput(responses.STDOUT, message); },
                      printErr: function(message) { postOutput(responses.STDERR, message); } });
// This creates an overall args array as ["-smtlib2", "input.smt2"]
args.push(INPUT_FNAME);
// This writes the required smtlib2 code to the emscripten virtual filesystem
solver.FS.writeFile(INPUT_FNAME, input, { encoding: "utf8" });
// Finally, runs the solver. The print / printErr function will be called as required
solver.callMain(args);
```

- Ok, when I try this and set ENVIRONMENT to WEB (after disabling eslint for the file), get this error `in the web, we need the wasm binary to be preloaded and set on Module['wasmBinary']. emcc.py will do that for you when generating HTML (but not JS)`
- If I use ENVIRONMENT as WORKER... 
- **WORKING**: Need to use a web worker (with `worker-loader`). Have to put the z3w.js and z3w.wasm files inside "public" folder, then modify the z3w.js file to link to http://localhost:3000/z3w.wasm instead of the original string of `z3w.wasm`.
