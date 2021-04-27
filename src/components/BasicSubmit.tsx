import React, { useState, useEffect } from 'react'


export const BasicSubmit: React.FC = () => {
    function onSubmit() {
        console.log("hi");
    }

    return (
        <div>
            <h1> Hi </h1>
            <button onClick={onSubmit}>Run</button>
        </div>
    );
}

