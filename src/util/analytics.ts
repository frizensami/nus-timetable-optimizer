import ReactGA from 'react-ga';
import { useEffect, useState } from 'react';
import { useLocation } from 'react-router-dom';
import { getCookieConsentValue } from 'react-cookie-consent';
import Cookies from 'universal-cookie';
import reportWebVitals from '../reportWebVitals';

export const BUTTON_CATEGORY = 'User Button Click';

// Doesn't have to be private since it's all clientside, and the UA ids aren't really secret.
export function initGA() {
    if (process.env.NODE_ENV === 'production') {
        console.log('Initializing production google analytics');
        ReactGA.initialize('UA-126704116-2');
    } else if (window.location.href.includes('localhost')) {
        console.log('Initializing local google analytics');
        ReactGA.initialize('UA-126704116-3');
    }
    // Initial page ping after an init
    ReactGA.pageview(window.location.pathname + window.location.search);

    // If you want to start measuring performance in your app, pass a function
    // to log results (for example: reportWebVitals(console.log))
    // or send to an analytics endpoint. Learn more: https://bit.ly/CRA-vitals
    reportWebVitals(sendWebVitalsToAnalytics);
}

export function removeGA() {
    const cookies = new Cookies();
    cookies.remove('_ga');
    cookies.remove('_gat');
    cookies.remove('_gid');
}

export function isCookieConsentGranted() {
    return getCookieConsentValue() === 'true';
}

export function isCookieQuestionAnswered() {
    return getCookieConsentValue() !== undefined;
}

// https://github.com/react-ga/react-ga/issues/301
// Hook to figure out which page the user is currently on. Previous method was heavily undercounting.
export function usePageTracking() {
    const location = useLocation();

    // Run initialization ONCE (this is for returning users that have already consented)
    useEffect(() => {
        if (isCookieConsentGranted()) {
            initGA();
        }
    }, []);

    // Try to send a pageview when location changes. If ReactGA is not initialized, won't do anything
    useEffect(() => {
        if (isCookieConsentGranted()) {
            ReactGA.pageview(location.pathname + location.search);
        }
    }, [location]);
}

// Web vitals function
export function sendWebVitalsToAnalytics({ id, name, value }: any) {
    ReactGA.event({
        category: 'Web Vitals',
        action: name,
        value: Math.round(name === 'CLS' ? value * 1000 : value), // values must be integers
        label: id, // id unique to current page load
        nonInteraction: true, // avoids affecting bounce rate
    });
}

// Record individual button clicks to see what's being used
export function recordButtonClick(buttonName: string, extraInfo: string = '') {
    if (isCookieConsentGranted()) {
        const eventDetails = {
            category: BUTTON_CATEGORY,
            action: `Clicked ${buttonName}`,
            label: extraInfo,
        };
        // console.log(eventDetails);
        ReactGA.event(eventDetails);
    }
}

// Record individual button clicks to see what's being used
export function recordPerf(
    category: string,
    variable: string,
    numMillis: number,
    extraInfo: string = ''
) {
    if (isCookieConsentGranted()) {
        const eventDetails = {
            category: category,
            variable: variable,
            value: numMillis,
            label: extraInfo,
        };
        // console.log(eventDetails);
        ReactGA.timing(eventDetails);
    }
}
