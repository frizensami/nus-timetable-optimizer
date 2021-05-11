import React, { useState, useEffect } from 'react'
import logo from './logo.svg';
// import './App.css';             
// import 'semantic-ui-less/semantic.less'

import Timetable from './Timetable'
import { Solver } from './Solver'
import { Divider, Message } from 'semantic-ui-react'

export const SolverApp: React.FC = () => {
    let [tt, setTT] = useState({})

    function onNewTimetable(timetable: any) {
        setTT(timetable);
    }

    return (
        <div>
            <Message error>
                <Message.Header as="p" style={{ "textAlign": "center" }}>
                    The NUS Modules Timetable Optimizer is in <em> Beta Testing Mode</em>. Please report any errors to <a href="mailto:sriramsami@nus.edu.sg?subject=NUS Modules Optimizer Error">sriramsami@nus.edu.sg</a>.
            </Message.Header>

            </Message>
            <Timetable start_hour={8} end_hour={22} timetable={tt} />
            <Divider />
            <Solver onNewTimetable={onNewTimetable} />
        </div>
    );
}
