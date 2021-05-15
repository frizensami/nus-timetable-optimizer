const smt = require('smtlib');
const SIM_VARNAME = 'weeks_to_simulate';
/**
 * Separate solver to solving the Hitting Set NP-Hard problem to find the minimum number of weeks to simulate.
 * We pass in all the weeks for each lesson as a bitvector, and this generates the smtlib2 string that solves for
 *  the minimum number of weeks to cover all weeks input so far.
 *
 *
 *  Mathematically:
 *      - Weeks = { 1...13 }
 *      - Simulated SUBSETOF Weeks
 *      - S = { S_i | S_i SUBSETOF Weeks is a list of weeks that a lesson must be held }
 *      - FORALL(S_i) IN S: S_i intersect Simulated != nullset
 * */
export class Z3WeekSolver {
    solver: any; // For the actual constraints
    num_weeks: number; // Defines bitvec sizes
    zero: string;
    one: string;

    constructor(num_weeks: number) {
        this.solver = new smt.BaseSolver('QF_ALL_SUPPORTED');
        this.num_weeks = num_weeks;
        this.zero = this._generate_zero();
        this.one = this._generate_one();
        this.solver.add(this._generate_decl(SIM_VARNAME)); // Add in our required "sim" variable
        this.solver.add(this._generate_popcnt()); // Add in the variable definition for popcount for this weeksize
    }

    add_weeks(weeks: Array<number>, id_str: string) {
        let values = new Array(this.num_weeks).fill(0);
        weeks.forEach((week: number) => (values[week - 1] = 1));
        this._declare_constraint(values, id_str);
    }

    generateSmtlib2String(): string {
        let constraintStr = '';
        this.solver.forEachStatement((stmt: string) => (constraintStr += stmt + '\n'));
        constraintStr = constraintStr.substring(constraintStr.indexOf('\n') + 1);
        const minimizeStr = `(minimize (popCount13 ${SIM_VARNAME}))\n`;
        // The string that executes the solver and retrives the final model and objectives
        let solveStr = `(check-sat)\n(get-value (${SIM_VARNAME}))\n(exit)`;
        // Overall SMTLIB2 string to return
        const finalStr = constraintStr + minimizeStr + solveStr;
        console.log(finalStr);
        return finalStr;
    }

    /**
     * Utils
     * */
    _declare_constraint(values: Array<number>, id_str: string) {
        const bv = this._generate_bitvec(values);
        this.solver.add(this._generate_decl(id_str));
        this.solver.assert(smt.Eq(id_str, bv));
        this.solver.assert(smt.NEq(smt.BVAnd(id_str, SIM_VARNAME), this.zero));
        // (assert (not (= (bvand x sim) zerovec)))
    }

    _generate_decl(varname: string): any {
        return smt.DeclareFun(varname, [], '(_ BitVec ' + this.num_weeks + ')');
    }

    _generate_bitvec(values: Array<number>) {
        if (values.length !== this.num_weeks) {
            throw new Error(
                'Programming error: the values array passed to this function must be consistent with the SMT Sort used (BitVec num_weeks)'
            );
        }
        let str = '#b' + values.map((val: number) => (val === 0 ? '0' : '1')).join('');
        return str;
    }

    _generate_popcnt() {
        const line1 = `(define-fun popCount13 ((x (_ BitVec ${this.num_weeks}))) (_ BitVec ${this.num_weeks})\n(bvadd\n`;
        let ites = '';
        for (let i = 0; i < this.num_weeks; i++) {
            ites += `(ite (= #b1 ((_ extract ${i} ${i}) x)) ${this.one} ${this.zero})\n`;
        }
        const end = `))`;
        return line1 + ites + end;
    }

    _generate_zero() {
        return this._generate_bitvec(new Array(this.num_weeks).fill(0));
    }

    _generate_one() {
        let arr = new Array(this.num_weeks).fill(0);
        arr[arr.length - 1] = 1;
        return this._generate_bitvec(arr);
    }
}
