import ReactGA from 'react-ga';

export const BUTTON_CATEGORY = 'User Button Click';

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
