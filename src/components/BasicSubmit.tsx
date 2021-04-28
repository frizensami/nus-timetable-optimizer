import React, { useState, useEffect } from 'react'

/* eslint-disable import/no-webpack-loader-syntax */
// @ts-ignore
import Z3Worker from "worker-loader!./z3worker.ts";

import { Z3Message, MessageKind } from "./z3Protocol"

import './BasicSubmit.css'


/*
 * BasicSubmit is a React Functional Component (FC)
 * It has to return a React Component.
 */
export const BasicSubmit: React.FC<{}> = () => {

    function receiveMessage(e: any) {
        const message: Z3Message = e.data
        console.log("Kind: %s, Message: %s", message.kind, message.msg)
    }

    function postMessage(worker: Worker, kind: MessageKind, msg: string) {
        const ctx: any = worker as any;
        let message: Z3Message = { kind: kind, msg: msg };
        ctx.postMessage(message);
    }

    function onSubmit() {
        console.log("Initializing z3 worker");

        let worker = new Z3Worker()
        worker.onmessage = receiveMessage;
        postMessage(worker, MessageKind.INIT, "");
        // console.log(worker)
    }

    return (
        <div className="content">
            <h1> Hi </h1>
            <button onClick={onSubmit}>Run</button>
        </div>
    );
}

