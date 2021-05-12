// -*- mode: typescript; indent-tabs-mode: nil; js-basic-offset: 4 -*-
//
// Copyright 2017-2020 Giovanni Campagna <gcampagn@cs.stanford.edu>
//
// See LICENSE for details

function stringEscape(str: string): string {
    return '"' + str.replace(/(["\\])/g, '\\$1').replace(/\n/g, '\\n') + '"';
    // the following comment fixes broken syntax highlighting in GtkSourceView
    //]/
}

export type SNode = SExpr | string;

class SExpr {
    private _children: SNode[];

    constructor(...children: SNode[]) {
        this._children = children;
    }

    toString(): string {
        return '(' + this._children.join(' ') + ')';
    }
}

function SetLogic(logic: string): SExpr {
    return new SExpr('set-logic', logic);
}
function SetOption(opt: string, value: SNode = 'true'): SExpr {
    return new SExpr('set-option', ':' + opt, value);
}
function DeclareDatatype(name: string, constructors: SNode[]): SExpr {
    const sortdec = new SExpr(name, '0');
    const datatypedec = new SExpr(...constructors.map((c) => Array.isArray(c) ? new SExpr(...c) : new SExpr(c)));

    return new SExpr('declare-datatypes', new SExpr(sortdec), new SExpr(datatypedec));
}
function DeclareSort(name: string): SExpr {
    return new SExpr('declare-sort', name, '0');
}
function DeclareFun(name: string, args: SNode[], ret: SNode): SExpr {
    return new SExpr('declare-fun', name, new SExpr(...args), ret);
}
function DefineFun(name: string, args: SNode[], ret: SNode, def: SNode): SExpr {
    return new SExpr('define-fun', name, new SExpr(...args), ret, def);
}
function Assert(assert: SNode): SExpr {
    return new SExpr('assert', assert);
}
function AssertSoft(assert: SNode, weight: number, id: string): SExpr {
    return new SExpr('assert-soft', assert, ":weight", weight.toString(), ":id", id);
}
function Predicate(pred: SNode, ...args: SNode[]): SNode {
    if (args.length === 0)
        return pred;
    else
        return new SExpr(pred, ...args);
}
function Implies(lhs: SNode, rhs: SNode): SExpr {
    return new SExpr('=>', lhs, rhs);
}
function If(conditional: SNode, iftrue: SNode, iffalse: SNode): SExpr {
    return new SExpr('ite', conditional, iftrue, iffalse);
}
function And(...args: SNode[]): SNode {
    if (args.length === 1)
        return args[0];
    return new SExpr('and', ...args);
}
function BVAnd(...args: SNode[]): SNode {
    if (args.length === 1)
        return args[0];
    return new SExpr('bvand', ...args);
}
function Or(...args: SNode[]): SNode {
    if (args.length === 1)
        return args[0];
    return new SExpr('or', ...args);
}
function Not(expr: SNode): SExpr {
    return new SExpr('not', expr);
}
function Eq(lhs: SNode, rhs: SNode): SExpr {
    return new SExpr('=', lhs, rhs);
}

//  ((_ pbeq N 1 1) SL_somename SL_somename2) ==> select N out of equally weighted SL_somename and SL_somename2
function PbEq(clauses: SNode[], weights: number[], N: number): SExpr {
    const strWeights = weights.map(x => x.toString());
    return new SExpr(new SExpr("_", "pbeq", N.toString(), ...strWeights), ...clauses);
}
//  ((_ pbge N 1 1) SL_somename SL_somename2) ==> select at least N out of equally weighted SL_somename and SL_somename2
function PbGe(clauses: SNode[], weights: number[], N: number): SExpr {
    const strWeights = weights.map(x => x.toString());
    return new SExpr(new SExpr("_", "pbge", N.toString(), ...strWeights), ...clauses);
}
//  ((_ pble N 1 1) SL_somename SL_somename2) ==> select at most N out of equally weighted SL_somename and SL_somename2
function PbLe(clauses: SNode[], weights: number[], N: number): SExpr {
    const strWeights = weights.map(x => x.toString());
    return new SExpr(new SExpr("_", "pble", N.toString(), ...strWeights), ...clauses);
}
function NEq(lhs: SNode, rhs: SNode): SExpr {
    return Not(Eq(lhs, rhs));
}
function LEq(lhs: SNode, rhs: SNode): SExpr {
    return new SExpr('<=', lhs, rhs);
}
function GEq(lhs: SNode, rhs: SNode): SExpr {
    return new SExpr('>=', lhs, rhs);
}
function LT(lhs: SNode, rhs: SNode): SExpr {
    return new SExpr('<', lhs, rhs);
}
function GT(lhs: SNode, rhs: SNode): SExpr {
    return new SExpr('>', lhs, rhs);
}
function SetType(elementType: SNode): SExpr {
    return new SExpr('Set', elementType);
}
function StringLiteral(str: string): SNode {
    return stringEscape(str);
}
function Named(name: SNode, expr: SNode): SExpr {
    return new SExpr('!', expr, ':named', name);
}
function Maximize(term: SNode): SExpr {
   return new SExpr('maximize', term) 
}
function Minimize(term: SNode): SExpr {
   return new SExpr('minimize', term) 
}
function Sum(...args: SNode[]): SNode {
    if (args.length === 1)
        return args[0];
    return new SExpr('+', ...args);
}
function CheckSat(): SExpr {
    return new SExpr('check-sat');
}

export {
    SExpr,
    SetLogic,
    SetOption,
    DeclareSort,
    DeclareDatatype,
    DeclareFun,
    DefineFun,
    Assert,
    AssertSoft,
    Predicate,
    Implies,
    And,
    BVAnd,
    Or,
    If,
    Not,
    Eq,
    PbEq,
    PbGe,
    PbLe,
    NEq,
    LEq,
    GEq,
    LT,
    GT,
    Named,
    SetType,
    StringLiteral,
    Maximize,
    Minimize,
    Sum,
    CheckSat
};
