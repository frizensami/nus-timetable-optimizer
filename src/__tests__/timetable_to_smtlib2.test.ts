import { LessonWeek, Lesson, Module, GenericTimetable } from '../core/generic_timetable'
import { TimetableSmtlib2Converter } from '../core/timetable_to_smtlib2'

test("Creates smtlib2 tables correctly", () => {
    const start_d = new Date(2018, 11, 12, 10, 30);
    const end_d = new Date(2018, 11, 12, 12, 30);
    let lesson = new Lesson("1", "Lecture", [[start_d, end_d]], ["Monday"], LessonWeek.ALL);
    let lesson2 = new Lesson("1", "Tutorial", [[start_d, end_d]], ["Tuesday"], LessonWeek.ALL);
    let mod = new Module("CS3203", 5, [lesson, lesson2], true);
    let mod2 = new Module("CS3210", 5, [lesson, lesson2], true);
    let gt = new GenericTimetable([mod, mod2], 5, 10);

    const converter = new TimetableSmtlib2Converter(gt, 100, 8, 16);
    const who_id_table = {
        CS3203__Lecture__1: 0,
        CS3203__Tutorial__1: 1024,
        CS3210__Lecture__1: 1048576,
        CS3210__Tutorial__1: 1049600
    }
    const r_who_id_table = {
        '0': 'CS3203__Lecture__1',
        '1024': 'CS3203__Tutorial__1',
        '1048576': 'CS3210__Lecture__1',
        '1049600': 'CS3210__Tutorial__1'
    }

    expect(converter.who_id_table).toEqual(who_id_table);
    expect(converter.reverse_who_id_table).toEqual(r_who_id_table);
});
