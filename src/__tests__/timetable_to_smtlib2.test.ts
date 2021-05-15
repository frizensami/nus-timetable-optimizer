import { Lesson, Module, GenericTimetable } from '../core/generic_timetable';
import { TimetableSmtlib2Converter } from '../core/timetable_to_smtlib2';
import { GlobalConstraintsList, defaultConstraints } from '../core/generic_timetable';
import { ALL_WEEKS } from '../core/constants';

test('Creates smtlib2 tables correctly', () => {
    const start_d = new Date(2018, 11, 12, 10, 30);
    const end_d = new Date(2018, 11, 12, 12, 30);
    let lesson = new Lesson('1', 'Lecture', [[start_d, end_d]], ['Monday'], ALL_WEEKS);
    let lesson2 = new Lesson('1', 'Tutorial', [[start_d, end_d]], ['Tuesday'], ALL_WEEKS);
    let mod = new Module('CS3203', 5, [lesson, lesson2], true);
    let mod2 = new Module('CS3210', 5, [lesson, lesson2], true);
    let gt = new GenericTimetable([mod, mod2], defaultConstraints);

    const converter = new TimetableSmtlib2Converter(gt, 100, 8, 16);
    const who_id_table = {
        CS3203__Lecture__1: 0,
        CS3203__Tutorial__1: 1024,
        CS3210__Lecture__1: 1048576,
        CS3210__Tutorial__1: 1049600,
    };
    const r_who_id_table = {
        '0': 'CS3203__Lecture__1',
        '1024': 'CS3203__Tutorial__1',
        '1048576': 'CS3210__Lecture__1',
        '1049600': 'CS3210__Tutorial__1',
    };

    expect(converter.who_id_table).toEqual(who_id_table);
    expect(converter.reverse_who_id_table).toEqual(r_who_id_table);
});

test('Creates smtlib2 string correctly for one module with one tutorial clashing with lecture (made-up scenario)', () => {
    // Lecture from 1030 to 1130
    let lesson = new Lesson(
        '1',
        'Lecture',
        [[new Date(2018, 11, 12, 10, 30), new Date(2018, 11, 12, 11, 30)]],
        ['Monday'],
        ALL_WEEKS
    );
    // Tutorial from 0930 to 1030
    let lesson2 = new Lesson(
        '1',
        'Tutorial',
        [[new Date(2018, 11, 12, 9, 30), new Date(2018, 11, 12, 10, 30)]],
        ['Monday'],
        ALL_WEEKS
    );
    // Tutorial from 1030 to 1130 (shouldn't work when we solve it)
    let lesson3 = new Lesson(
        '2',
        'Tutorial',
        [[new Date(2018, 11, 12, 10, 30), new Date(2018, 11, 12, 11, 30)]],
        ['Monday'],
        ALL_WEEKS
    );
    let mod = new Module('CS3203', 5, [lesson, lesson2, lesson3], true);
    let gt = new GenericTimetable([mod], defaultConstraints);

    // Timetable of only 5 hours, starting at 8 am and ending at 10 pm on a Monday (monday since we restrict # of half hour slots)
    const converter = new TimetableSmtlib2Converter(gt, 10, 8, 22);
    const smtlib2str = converter.generateTimetableSolveSmtLib2String(false);
    const smtlib2str_expected = `(declare-fun SL_CS3203__Lecture__1 () Int)
(declare-fun t5_monday_1030_wk0 () Int)
(declare-fun t6_monday_1100_wk0 () Int)
(declare-fun SL_CS3203__Tutorial__1_CS3203__Tutorial__2 () Int)
(declare-fun t3_monday_0930_wk0 () Int)
(declare-fun t4_monday_1000_wk0 () Int)
(assert (= SL_CS3203__Lecture__1 0))
(assert (= (= SL_CS3203__Lecture__1 0) (= t5_monday_1030_wk0 0)))
(assert (= (= SL_CS3203__Lecture__1 0) (= t6_monday_1100_wk0 0)))
(assert (or (= SL_CS3203__Tutorial__1_CS3203__Tutorial__2 1024) (= SL_CS3203__Tutorial__1_CS3203__Tutorial__2 1025)))
(assert (= (= SL_CS3203__Tutorial__1_CS3203__Tutorial__2 1024) (= t3_monday_0930_wk0 1024)))
(assert (= (= SL_CS3203__Tutorial__1_CS3203__Tutorial__2 1024) (= t4_monday_1000_wk0 1024)))
(assert (= (= SL_CS3203__Tutorial__1_CS3203__Tutorial__2 1025) (= t5_monday_1030_wk0 1025)))
(assert (= (= SL_CS3203__Tutorial__1_CS3203__Tutorial__2 1025) (= t6_monday_1100_wk0 1025)))
(assert (or (= t5_monday_1030_wk0 0) (= t5_monday_1030_wk0 -1) (= t5_monday_1030_wk0 1025)))
(assert (or (= t6_monday_1100_wk0 0) (= t6_monday_1100_wk0 -1) (= t6_monday_1100_wk0 1025)))
(assert (or (= t3_monday_0930_wk0 1024) (= t3_monday_0930_wk0 -1)))
(assert (or (= t4_monday_1000_wk0 1024) (= t4_monday_1000_wk0 -1)))
(declare-fun BUGFIX_VAR_DONTASK () Int)
(assert-soft (= BUGFIX_VAR_DONTASK 10))
(check-sat)
(get-model)
(get-objectives)
(exit)`;

    expect(smtlib2str).toEqual(smtlib2str_expected);
});
