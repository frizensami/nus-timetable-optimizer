import React from 'react';
import logo from './logo.svg';
// import './App.css';             
import 'semantic-ui-less/semantic.less'

import Timetable from './components/Timetable'
import { Solver } from './components/Solver'
import { Divider } from 'semantic-ui-react'

function App() {
    return (
        <div className="App">
            <div className="ui basic segment">
                <h1 className="ui center aligned header"> NUSMods Timetable Arranger </h1>
                <Timetable start_hour={8} end_hour={22} />
                <Divider/>
                <Solver />
            </div>
        </div>
        // <div className="App">
        //   <header className="App-header">
        //     <img src={logo} className="App-logo" alt="logo" />
        //     <p>
        //       Edit <code>src/App.tsx</code> and save to reload.
        //     </p>
        //     <a
        //       className="App-link"
        //       href="https://reactjs.org"
        //       target="_blank"
        //       rel="noopener noreferrer"
        //     >
        //       Learn React
        //     </a>
        //   </header>
        // </div>
    );
}

export default App;
