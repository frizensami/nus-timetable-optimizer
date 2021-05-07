import React, { useState, useEffect } from 'react'
import logo from './logo.svg';
// import './App.css';             
import 'semantic-ui-less/semantic.less'

import Timetable from './components/Timetable'
import { Solver } from './components/Solver'
import { Divider } from 'semantic-ui-react'

function App() {
        let [tt, setTT] = useState({})

        function onNewTimetable(timetable: any) {
                setTT(timetable);
        }

        return (
                <div className="App">
                        <div className="ui basic segment">
                                <h1 className="ui center aligned header"> NUSMods Timetable Optimizer </h1>
                                <Timetable start_hour={8} end_hour={22} timetable={tt} />
                                <Divider />
                                <Solver onNewTimetable={onNewTimetable}/>
                        </div>
                </div>
        );
}

export default App;
