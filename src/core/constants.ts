import { flipRecord } from '../util/utils'

export const DAYS = 6  // One week mon - sat
export const DAY_START_HOUR = 8
export const DAY_END_HOUR = 22
export const HOURS_PER_DAY = DAY_END_HOUR - DAY_START_HOUR  // 14 8 am --> 10 pm

export const DAY_IDXS: Record<string, number> = {
    "monday": 0,
    "tuesday": 1,
    "wednesday": 2,
    "thursday": 3,
    "friday": 4,
    "saturday": 5,
}

export const IDX_DAYS = flipRecord(DAY_IDXS);
