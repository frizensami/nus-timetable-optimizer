import React, { useState, useEffect } from 'react'
import logo from './logo.svg';
// import './App.css';             
import 'semantic-ui-less/semantic.less'

import Timetable from './Timetable'
import { Solver } from './Solver'
import { Divider } from 'semantic-ui-react'

export const SolverApp: React.FC = () => {
    let [tt, setTT] = useState({})

    function onNewTimetable(timetable: any) {
        setTT(timetable);
    }

    return (
        <div>
            <Timetable start_hour={8} end_hour={22} timetable={tt} />
            <Divider />
            <Solver onNewTimetable={onNewTimetable} />
        </div>
    );
}
