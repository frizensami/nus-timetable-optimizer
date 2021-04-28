import React, { useState, useEffect } from 'react'

/* eslint-disable import/no-webpack-loader-syntax */
// @ts-ignore
import Z3Worker from "worker-loader!./z3worker.js";

import './BasicSubmit.css'


/*
 * BasicSubmit is a React Functional Component (FC)
 * It has to return a React Component.
 */
export const BasicSubmit: React.FC<{}> = () => {

    function receiveMessage(e: any) {
        const data = e.data
        console.log(data) 
    }

    function onSubmit() {
        console.log("Initializing z3");

        let worker = new Z3Worker()
        worker.onmessage = receiveMessage;
        worker.postMessage("ASDASD");
        // console.log(worker)
    }

  

    return (
        <div className="content">
            <h1> Hi </h1>
            <button onClick={onSubmit}>Run</button>
        </div>
    );
}

