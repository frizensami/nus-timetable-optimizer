import { TimetableOutput, TimetableSmtlib2Converter } from './timetable_to_smtlib2'
import { GenericTimetable } from './generic_timetable'
import { Z3Message, MessageKind } from "./z3_protocol"

/* eslint-disable import/no-webpack-loader-syntax */
// @ts-ignore
import Z3Worker from "worker-loader!./z3_worker";

const DAYS = 5  // One week
const HOURS_PER_DAY = 14  // 8 am --> 10 pm
const DAY_START_HOUR = 8
const DAY_END_HOUR = 22

/**
 * The Z3 manager takes a generic timetable as input and manages the lifecycle of running the
 * Z3 system to find a timetable solution.
 * Runs the web worker, receives input/output, communicates through callbacks to the calling class.
 *
 * Only one Z3 Manager per application - allows stateless components to run manager methods
 * */
export class Z3Manager {
    static gt: GenericTimetable
    static conv: TimetableSmtlib2Converter
    static smtString: string
    static callbacks: Z3Callbacks
    static printBuffer: string
    static errBuffer: string
    static worker?: Z3Worker = null;


    static initZ3(callbacks: Z3Callbacks) {
        Z3Manager.callbacks = callbacks;
        Z3Manager.printBuffer = "";
        Z3Manager.errBuffer = "";
        // Set up worker if it's not set up
        if (!Z3Manager.worker) {
            Z3Manager.worker = new Z3Worker()
            Z3Manager.worker.onmessage = Z3Manager.receiveWorkerMessage;
        }
        Z3Manager.managerPostMessage(MessageKind.INIT, "");
    }


    /** 
     * Register a generic timetable a set of callbacks to be called for different states in the Z3 solver lifecycle
     * */
    static loadTimetable(gt: GenericTimetable) {
        console.log("Loaded timetable")
        console.log(gt)
        Z3Manager.gt = gt;
        Z3Manager.conv = new TimetableSmtlib2Converter(Z3Manager.gt,
            DAYS * HOURS_PER_DAY * 2, // Number of "half-hour" slots
            DAY_START_HOUR, // Start at 8am
            DAY_END_HOUR) // End at 2200 (10 pm)
        Z3Manager.smtString = Z3Manager.conv.generateSmtLib2String();
        // Run callback to update the generated smtlib2 string
        Z3Manager.callbacks.onSmtlib2InputCreated(Z3Manager.smtString)
        Z3Manager.printBuffer = "";
        Z3Manager.errBuffer = "";
    }


    static solve() {
        Z3Manager.managerPostMessage(MessageKind.OPTIMIZE, Z3Manager.smtString);
    }


    static receiveWorkerMessage(e: any) {
        const message: Z3Message = e.data
        // console.log("Kind: %s, Message: %s", message.kind, message.msg)
        switch (message.kind) {
            case MessageKind.INITIALIZED:
                // Call the initialization callback
                Z3Manager.callbacks.onZ3Initialized();
                break;
            case MessageKind.PRINT:
                Z3Manager.printBuffer += message.msg + "\n"
                break;
            case MessageKind.ERR:
                Z3Manager.errBuffer += message.msg + "\n"
                break;
            case MessageKind.EXIT:
                console.log("Z3 messages on exit: ")
                if (Z3Manager.printBuffer === "" && Z3Manager.errBuffer === "") {
                    console.log("Premature exit - Z3 was initializing (this is normal)")
                    return; // Premature exit (probably initialization)
                }
                if (Z3Manager.printBuffer !== "") {
                    console.log(Z3Manager.printBuffer);
                }
                if (Z3Manager.errBuffer !== "") {
                    console.error(Z3Manager.errBuffer);
                }
                // Call the output callback
                Z3Manager.callbacks.onOutput(Z3Manager.printBuffer + "\n" + Z3Manager.errBuffer);
                // Process the output text we just got from the Z3 solver
                const timetable: TimetableOutput = Z3Manager.conv.z3_output_to_timetable(Z3Manager.printBuffer);
                Z3Manager.callbacks.onTimetableOutput(timetable);
                break;
            default:
                break;
        }
    }

    /**
     * Generically post a message of the assigned Z3 Protocol to the worker
     * */
    static managerPostMessage(kind: MessageKind, msg: string) {
        let message: Z3Message = { kind: kind, msg: msg };
        Z3Manager.worker.postMessage(message);
    }

}

export interface Z3Callbacks {
    onZ3Initialized: any
    onSmtlib2InputCreated(s: string): any
    onOutput(s: string): any
    onTimetableOutput(timetable: TimetableOutput): any
}
