# NUSMods Timetable Arranger - Web Version

## Objectives
- Allow users to arrange their NUS timetable based on constraints (keep lunch-time free, no classes before 9 am, etc.)
- This system should run primarily on the user's infrastructure (i.e., in their browser) to keep server load low. This is necessary due to the CPU-heavy SMT solver method being used.

## Architecture
- **React frontend** that should call little to no APIs on the backend that serves it (i.e., backend should primarily exist just to serve the app as-is)
- Frontend should take in user timetable and constraints (keep it to an MVP-level frontend for now) and **convert those into SMTLIB2 code**
- Frontend should then **call the z3 wasm binary** that will execute the SMTLIB2 code and read + format the results


## Building and Running
- `src/z3` was downloaded from the initial release [here](https://github.com/cpitclaudel/z3.wasm/releases), since building it was error-prone
