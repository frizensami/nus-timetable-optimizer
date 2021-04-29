import React, { useState, useEffect } from 'react'

/* eslint-disable import/no-webpack-loader-syntax */
// @ts-ignore
import Z3Worker from "worker-loader!./z3worker.ts";

import { Z3Message, MessageKind } from "./z3Protocol"

import './BasicSubmit.css'

import { smtTest } from '../core/smt_test'


/*
 * BasicSubmit is a React Functional Component (FC)
 * It has to return a React Component.
 */
export const BasicSubmit: React.FC<{}> = () => {

    let worker: any = null;

    const testSmt = `
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun z () Int)
        (assert (>= (* 2 x) (+ y z)))
        (declare-fun f (Int) Int)
        (declare-fun g (Int Int) Int)
        (assert (< (f x) (g x x)))
        (assert (> (f y) (g x x)))
        (check-sat)
        (get-model)
        (push)
        (assert (= x y))
        (check-sat)
        (get-model)
        (check-sat)
        (pop)
        (exit)
    `;

    function receiveWorkerMessage(e: any) {
        const message: Z3Message = e.data
        console.log("Kind: %s, Message: %s", message.kind, message.msg)
        switch (message.kind) {
            case MessageKind.INITIALIZED:
                console.log("Z3 Initialized!");
                postMessage(worker, MessageKind.OPTIMIZE, testSmt);
                break;
            case MessageKind.PRINT:
                console.log("Message from Z3 solver: ");
                console.log(message.msg)
                break;
            case MessageKind.ERR:
                console.error("Error from Z3 Solver: ");
                console.error(message.msg)
                break;
            default:
                break;
        }
    }

    function postMessage(worker: Worker, kind: MessageKind, msg: string) {
        let message: Z3Message = { kind: kind, msg: msg };
        worker.postMessage(message);
    }

    function onSubmit() {
        console.log("Initializing z3 worker");
        // worker = new Z3Worker()
        // worker.onmessage = receiveWorkerMessage;
        // postMessage(worker, MessageKind.INIT, "");

        console.log(smtTest());
        // console.log(worker)
    }

    return (
        <div className="content">
            <h1> Hi </h1>
            <button onClick={onSubmit}>Run</button>
        </div>
    );
}

