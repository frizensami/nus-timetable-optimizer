import React, { useState, useEffect } from 'react'
import { Segment, Button, Container, Divider, Grid, Loader, Dimmer, Header } from 'semantic-ui-react'
import logo from './logo.svg';
// import './App.css';             
// import 'semantic-ui-less/semantic.less'


export const About: React.FC = () => {
    return (
        <Container text textAlign='justified'>
            <Segment raised>
                <Header as="h2" textAlign="center"> About </Header>

                <Header as="h3" textAlign="left"> Who are you? </Header>
                <p> {"I'm"} Sriram, a PhD student at the NUS School of Computing. You can find me at <a href="https://sriramsami.com" target="_blank">sriramsami.com</a>.</p>

                <Header as="h3" textAlign="left"> Why do this? </Header>
                <p> {"I've"} always wondered if I've extracted the maximum laziness out of my timetables.
                    I don't need to optimize my own timetables anymore, but this could still be useful to other people!  </p>

                <Header as="h3" textAlign="left"> Is this project affiliated with NUSMods? </Header>
                <p> No. However, NUSMods have a wonderful public-facing API at <a target="_blank" href="https://api.nusmods.com/v2/">{"https://api.nusmods.com/v2/"}</a> that this optimizer uses, and that I am very grateful for.
                    All API requests for module information are cached locally for a while to avoid hitting the API too much. </p>

                <Header as="h3" textAlign="left"> Is this a new idea? </Header>
                <p> Yes and no. There have been a number of attempts (including my own previous one in 2015) to address this issue.
                This work is most closely inspired by <a target="_blank" href="https://modsplanner.tk">{"https://modsplanner.tk/"}</a>, which appears to be defunct.
            I would urge anyone interested to see the modsplanner {"team's"} technical report and work on <a target="_blank" href="https://github.com/raynoldng/nusmods-planner">their GitHub page</a>.
            </p>

                <Header as="h3" textAlign="left"> {"What's innovative about this system?"} </Header>
                <p>
                    The aim of this project was to do almost no computation on the server, and let clients (i.e., your browsers) do all of the heavy lifting.
                    The solver used in this project can be very CPU-intensive to run, so this project would not scale well if the server was processing optimizations
                    for many clients at the same time. It would also cost a fortune to host.
            </p>

                <p>
                    <strong> This work allows the optimizer to run on browsers at speeds that are very close to running it natively on a computer</strong>.
                This is mainly due to the amazing effort by <a target="_blank" href="http://pit-claudel.fr/clement/">Clément Pit-Claudel</a> at MIT to enable the
                <a target="_blank" href="https://github.com/Z3Prover/z3"><strong> Microsoft Z3 solver</strong></a> to be run as a <a target="_blank" href="https://webassembly.org/">WebAssembly</a> module.
            </p>

            
                <Header as="h3" textAlign="left"> {"What technology enables this system?"} </Header>
                <p> The core of this system is the
                <a target="_blank" href="https://github.com/Z3Prover/z3"><strong> Microsoft Z3 SMT (Satisfiability Modulo Theories) solver</strong></a>, an incredible piece of work that 
                enables a class of difficult problems to be solved quickly, <i>if the problem can be encoded correctly</i>.
                To run Z3 on the browser, I use the pre-release WebAssembly binaries and glue code from
                <a target="_blank" href="https://github.com/cpitclaudel/z3.wasm"> the z3.wasm project</a>. The front-end is built using <a target="_blank" href="https://reactjs.org/">React</a>.</p> 

            </Segment>
        </Container>
    );
}
