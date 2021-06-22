import * as analytics from '../util/analytics';
import ReactGA from 'react-ga';

// Initialize test mode APi
beforeEach(() => {
    ReactGA.initialize('foo', { testMode: true });
});

// Reset all API calls
afterEach(() => {
    ReactGA.testModeAPI.calls.length = 0;
});

test('Button analytics are sent appropriately when extra info not specified', () => {
    analytics.recordButtonClick('Run Optimizer');
    expect(ReactGA.testModeAPI.calls).toContainEqual([
        'send',
        {
            eventCategory: analytics.BUTTON_CATEGORY,
            eventAction: 'Clicked Run Optimizer',
            hitType: 'event',
        },
    ]);
});

test('Button analytics are sent appropriately when extra info IS specified', () => {
    analytics.recordButtonClick('Run Optimizer', 'Failed');
    expect(ReactGA.testModeAPI.calls).toContainEqual([
        'send',
        {
            eventCategory: analytics.BUTTON_CATEGORY,
            eventAction: 'Clicked Run Optimizer',
            eventLabel: 'Failed',
            hitType: 'event',
        },
    ]);
});

test('Button analytics are sent appropriately for share link', () => {
    const shareUrl =
        'https://nusmods.com/timetable/sem-1/share?CS1101S=REC:01,TUT:03C,LEC:1&CS6219=&LSM1301=LEC:1,LAB:3';
    analytics.recordButtonClick('Add Modules From Link', `Success: ${shareUrl}`);
    expect(ReactGA.testModeAPI.calls).toContainEqual([
        'send',
        {
            eventCategory: analytics.BUTTON_CATEGORY,
            eventAction: 'Clicked Add Modules From Link',
            eventLabel: `Success: ${shareUrl}`,
            hitType: 'event',
        },
    ]);
});

test('Z3 timer analytics should be correctly sent', () => {
    analytics.recordPerf('Z3', 'initTime', 10205);
    expect(ReactGA.testModeAPI.calls).toContainEqual([
        'send',
        {
            timingCategory: 'Z3',
            timingVar: 'initTime',
            timingValue: 10205,
            hitType: 'timing',
        },
    ]);
});
