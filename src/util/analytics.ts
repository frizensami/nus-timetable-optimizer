import ReactGA from 'react-ga';
import { useEffect, useState } from 'react';
import { useLocation } from 'react-router-dom';

export const BUTTON_CATEGORY = 'User Button Click';

// https://github.com/react-ga/react-ga/issues/301
// Hook to figure out which page the user is currently on. Previous method was heavily undercounting.
export const usePageTracking = () => {
    const location = useLocation();
    const [initialized, setInitialized] = useState(false);

    // Run initialization ONCE
    useEffect(() => {
        if (process.env.NODE_ENV === 'production') {
            ReactGA.initialize('UA-126704116-2');
        } else if (window.location.href.includes('localhost')) {
            ReactGA.initialize('UA-126704116-3');
        }
        setInitialized(true);
    }, []);

    // If initialization state or location state changes, send out a pageview
    useEffect(() => {
        if (initialized) {
            ReactGA.pageview(location.pathname + location.search);
        }
    }, [initialized, location]);
};

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
    const eventDetails = {
        category: BUTTON_CATEGORY,
        action: `Clicked ${buttonName}`,
        label: extraInfo,
    };
    // console.log(eventDetails);
    ReactGA.event(eventDetails);
}

// Record individual button clicks to see what's being used
export function recordPerf(
    category: string,
    variable: string,
    numMillis: number,
    extraInfo: string = ''
) {
    const eventDetails = {
        category: category,
        variable: variable,
        value: numMillis,
        label: extraInfo,
    };
    // console.log(eventDetails);
    ReactGA.timing(eventDetails);
}
