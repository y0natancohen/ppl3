// L4-eval-box.ts
// L4 with mutation (set!) and env-box model
// Direct evaluation of letrec with mutation, define supports mutual recursion.

import {map, reduce, repeat, zipWith, filter} from "ramda";
import {allT, first, rest, isBoolean, isEmpty, isNumber, isString} from "./list";
import {getErrorMessages, hasNoError, isError} from "./error";
import {
    isBoolExp, isCExp, isLitExp, isNumExp, isPrimOp, isStrExp, isVarRef, isSetExp,
    isAppExp, isDefineExp, isExp, isIfExp, isLetrecExp, isLetExp, isProcExp, isProgram,
    Binding, PrimOp, VarDecl, CExp, Exp, IfExp, LetrecExp, LetExp, Parsed, ProcExp, Program, SetExp,
    parse, unparse
} from "./L4-ast";
import {
    applyEnv,
    applyEnvBdg,
    globalEnvAddBinding,
    makeExtEnv,
    setFBinding,
    theGlobalEnv,
    Env,
    persistentEnv,
    FBinding,
    isExtEnv,
    isFrame,
    unbox,
    isGlobalEnv,
    BodyId, generateBodyId
} from "./L4-env-box";
import {
    isEmptySExp, isSymbolSExp, isClosure, isCompoundSExp, makeClosure, makeCompoundSExp, Closure,
    CompoundSExp, EmptySExp, makeEmptySExp, Value, makeClosureBodyId, ClosureBodyId, makeClosure1
} from "./L4-value-box";
import {Edge, Graph} from "graphlib";
import dot = require("graphlib-dot");
import * as graphlib from "graphlib";
import * as util from "util";
import {astToDot} from "../part2/graph-ast";

// ========================================================
// Eval functions

const applicativeEval = (exp: CExp | Error, env: Env): Value | Error =>
    isError(exp) ? exp :
        isNumExp(exp) ? exp.val :
            isBoolExp(exp) ? exp.val :
                isStrExp(exp) ? exp.val :
                    isPrimOp(exp) ? exp :
                        isVarRef(exp) ? applyEnv(env, exp.var) :
                            isLitExp(exp) ? exp.val :
                                isIfExp(exp) ? evalIf(exp, env) :
                                    isProcExp(exp) ? evalProc(exp, env) :
                                        isLetExp(exp) ? evalLet(exp, env) :
                                            isLetrecExp(exp) ? evalLetrec(exp, env) :
                                                isSetExp(exp) ? evalSet(exp, env) :
                                                    isAppExp(exp) ? applyProcedure(applicativeEval(exp.rator, env),
                                                        map((rand: CExp) => applicativeEval(rand, env),
                                                            exp.rands), env) :
                                                        Error(`Bad L4 AST ${exp}`);

const applicativeEval1 = (exp: CExp | Error, env: Env): Value | Error =>
    isError(exp) ? exp :
        isNumExp(exp) ? exp.val :
            isBoolExp(exp) ? exp.val :
                isStrExp(exp) ? exp.val :
                    isPrimOp(exp) ? exp :
                        isVarRef(exp) ? applyEnv(env, exp.var) :
                            isLitExp(exp) ? exp.val :
                                isIfExp(exp) ? evalIf(exp, env) :
                                    isProcExp(exp) ? evalProc1(exp, env) : // change is here
                                        isLetExp(exp) ? evalLet(exp, env) :
                                            isLetrecExp(exp) ? evalLetrec(exp, env) :
                                                isSetExp(exp) ? evalSet(exp, env) :
                                                    isAppExp(exp) ? applyProcedure(applicativeEval(exp.rator, env),
                                                        map((rand: CExp) => applicativeEval(rand, env),
                                                            exp.rands), env) :
                                                        Error(`Bad L4 AST ${exp}`);

export const isTrueValue = (x: Value | Error): boolean | Error =>
    isError(x) ? x :
        !(x === false);

const evalIf = (exp: IfExp, env: Env): Value | Error => {
    const test = applicativeEval(exp.test, env);
    return isError(test) ? test :
        isTrueValue(test) ? applicativeEval(exp.then, env) :
            applicativeEval(exp.alt, env);
};

const evalProc = (exp: ProcExp, env: Env): Closure => {
    return makeClosure(exp.args, exp.body, env);
};
const evalProc1 = (exp: ProcExp, env: Env): Closure => {
    return makeClosure1(exp.args, exp.body, env);
};

// @Pre: none of the args is an Error (checked in applyProcedure)
// KEY: This procedure does NOT have an env parameter.
//      Instead we use the env of the closure.
const applyProcedure = (proc: Value | Error, args: Array<Value | Error>, returnEnv: Env): Value | Error =>
    isError(proc) ? proc :
        !hasNoError(args) ? Error(`Bad argument: ${getErrorMessages(args)}`) :
            isPrimOp(proc) ? applyPrimitive(proc, args) :
                isClosure(proc) ? applyClosure(proc, args, returnEnv) :
                    Error(`Bad procedure ${JSON.stringify(proc)}`);

const applyClosure = (proc: Closure, args: Value[], returnEnv: Env): Value | Error => {
    let vars = map((v: VarDecl) => v.var, proc.params);
    let extendedEnv = makeExtEnv(vars, args, proc.env, returnEnv);
    persistentEnv[extendedEnv.id] = extendedEnv;
    return evalExps(proc.body, extendedEnv);
};

// Evaluate a sequence of expressions (in a program)
export const evalExps = (exps: Exp[], env: Env): Value | Error =>
    isEmpty(exps) ? Error("Empty program") :
        isDefineExp(first(exps)) ? evalDefineExps(first(exps), rest(exps)) :
            evalCExps(first(exps), rest(exps), env);

const evalCExps = (exp1: Exp, exps: Exp[], env: Env): Value | Error =>
    isCExp(exp1) && isEmpty(exps) ? applicativeEval(exp1, env) :
        isCExp(exp1) ? (isError(applicativeEval(exp1, env)) ? Error("error") :
            evalExps(exps, env)) :
            Error("Never");

export const evalExps1 = (exps: Exp[], env: Env): Value | Error =>
    isEmpty(exps) ? Error("Empty program") :
        isDefineExp(first(exps)) ? evalDefineExps1(first(exps), rest(exps)) :
            evalCExps1(first(exps), rest(exps), env);

const evalCExps1 = (exp1: Exp, exps: Exp[], env: Env): Value | Error =>
    isCExp(exp1) && isEmpty(exps) ? applicativeEval1(exp1, env) :
        isCExp(exp1) ? (isError(applicativeEval1(exp1, env)) ? Error("error") :
            evalExps1(exps, env)) :
            Error("Never");

// Eval a sequence of expressions when the first exp is a Define.
// Compute the rhs of the define, extend the env with the new binding
// then compute the rest of the exps in the new env.
// L4-BOX @@
// define always updates theGlobalEnv
// We also only expect defineExps at the top level.
const evalDefineExps = (def: Exp, exps: Exp[]): Value | Error => {
    if (isDefineExp(def)) {
        let rhs = applicativeEval(def.val, theGlobalEnv);
        if (isError(rhs))
            return rhs;
        else {
            globalEnvAddBinding(def.var.var, rhs);
            return evalExps(exps, theGlobalEnv);
        }
    } else {
        return Error("unexpected " + def);
    }
};
const evalDefineExps1 = (def: Exp, exps: Exp[]): Value | Error => {
    if (isDefineExp(def)) {
        let rhs = applicativeEval1(def.val, theGlobalEnv);
        if (isError(rhs))
            return rhs;
        else {
            globalEnvAddBinding(def.var.var, rhs);
            return evalExps1(exps, theGlobalEnv);
        }
    } else {
        return Error("unexpected " + def);
    }
};

// Main program
// L4-BOX @@ Use GE instead of empty-env
export const evalProgram = (program: Program): Value | Error =>
    evalExps(program.exps, theGlobalEnv);
export const evalProgram1 = (program: Program): Value | Error =>
    evalExps1(program.exps, theGlobalEnv);

export const evalParse = (s: string): Value | Error => {
    let ast: Parsed | Error = parse(s);
    if (isProgram(ast)) {
        return evalProgram(ast);
    } else if (isExp(ast)) {
        return evalExps([ast], theGlobalEnv);
    } else {
        return ast;
    }
};

export const evalParse1 = (s: string): Value | Error => {
    let ast: Parsed | Error = parse(s);
    if (isProgram(ast)) {
        return evalProgram1(ast);
    } else if (isExp(ast)) {
        return evalExps1([ast], theGlobalEnv);
    } else {
        return ast;
    }
};

// LET: Direct evaluation rule without syntax expansion
// compute the values, extend the env, eval the body.
const evalLet = (exp: LetExp, env: Env): Value | Error => {
    const vals = map((v: CExp) => applicativeEval(v, env), map((b: Binding) => b.val, exp.bindings));
    const vars = map((b: Binding) => b.var.var, exp.bindings);
    if (hasNoError(vals)) {
        let newEnv = makeExtEnv(vars, vals, env, env);
        persistentEnv[newEnv.id] = newEnv;
        return evalExps(exp.body, newEnv);
    } else {
        return Error(getErrorMessages(vals));
    }
};

// @@ L4-EVAL-BOX
// LETREC: Direct evaluation rule without syntax expansion
// 1. extend the env with vars initialized to void (temporary value)
// 2. compute the vals in the new extended env
// 3. update the bindings of the vars to the computed vals
// 4. compute body in extended env
const evalLetrec = (exp: LetrecExp, env: Env): Value | Error => {
    const vars = map((b: Binding) => b.var.var, exp.bindings);
    const vals = map((b: Binding) => b.val, exp.bindings);
    const extEnv = makeExtEnv(vars, repeat(undefined, vars.length), env, env);
    // @@ Compute the vals in the extended env
    const cvals = map((v: CExp) => applicativeEval(v, extEnv), vals);
    if (hasNoError(cvals)) {
        // Bind vars in extEnv to the new values
        zipWith((bdg, cval) => setFBinding(bdg, cval), extEnv.frame.fbindings, cvals);
        return evalExps(exp.body, extEnv);
    } else {
        return Error(getErrorMessages(cvals));
    }
};

// L4-eval-box: Handling of mutation with set!
const evalSet = (exp: SetExp, env: Env): Value | Error => {
    const v = exp.var.var;
    const val = applicativeEval(exp.val, env);
    if (isError(val))
        return val;
    else {
        const bdg = applyEnvBdg(env, v);
        if (isError(bdg)) {
            return Error(`Var not found ${v}`)
        } else {
            setFBinding(bdg, val);
            return undefined;
        }
    }
};

// ========================================================
// Primitives

const zero: number = 0;
const one: number = 1;

// @Pre: none of the args is an Error (checked in applyProcedure)
// TODO: Add explicit type checking in all primitives
export const applyPrimitive = (proc: PrimOp, args: Value[]): Value | Error =>
    proc.op === "+" ? (allT(isNumber, args) ? reduce((x: number, y: number) => x + y, zero, args) : Error("+ expects numbers only")) :
        proc.op === "-" ? minusPrim(args) :
            proc.op === "*" ? (allT(isNumber, args) ? reduce((x: number, y: number) => x * y, one, args) : Error("* expects numbers only")) :
                proc.op === "/" ? divPrim(args) :
                    proc.op === ">" ? ((allT(isNumber, args) || allT(isString, args)) ? args[0] > args[1] : Error("> expects numbers or strings only")) :
                        proc.op === "<" ? ((allT(isNumber, args) || allT(isString, args)) ? args[0] < args[1] : Error("< expects numbers or strings only")) :
                            proc.op === "=" ? args[0] === args[1] :
                                proc.op === "not" ? !args[0] :
                                    proc.op === "and" ? isBoolean(args[0]) && isBoolean(args[1]) && args[0] && args[1] :
                                        proc.op === "or" ? isBoolean(args[0]) && isBoolean(args[1]) && (args[0] || args[1]) :
                                            proc.op === "eq?" ? eqPrim(args) :
                                                proc.op === "string=?" ? args[0] === args[1] :
                                                    proc.op === "cons" ? consPrim(args[0], args[1]) :
                                                        proc.op === "car" ? carPrim(args[0]) :
                                                            proc.op === "cdr" ? cdrPrim(args[0]) :
                                                                proc.op === "list" ? listPrim(args) :
                                                                    proc.op === "list?" ? isListPrim(args[0]) :
                                                                        proc.op === "pair?" ? isPairPrim(args[0]) :
                                                                            proc.op === "number?" ? typeof (args[0]) === 'number' :
                                                                                proc.op === "boolean?" ? typeof (args[0]) === 'boolean' :
                                                                                    proc.op === "symbol?" ? isSymbolSExp(args[0]) :
                                                                                        proc.op === "string?" ? isString(args[0]) :
                                                                                            Error("Bad primitive op " + proc.op);

const minusPrim = (args: Value[]): number | Error => {
    // TODO complete
    let x = args[0], y = args[1];
    if (isNumber(x) && isNumber(y)) {
        return x - y;
    } else {
        return Error(`Type error: - expects numbers ${args}`)
    }
};

const divPrim = (args: Value[]): number | Error => {
    // TODO complete
    let x = args[0], y = args[1];
    if (isNumber(x) && isNumber(y)) {
        return x / y;
    } else {
        return Error(`Type error: / expects numbers ${args}`)
    }
};

const eqPrim = (args: Value[]): boolean | Error => {
    let x = args[0], y = args[1];
    if (isSymbolSExp(x) && isSymbolSExp(y)) {
        return x.val === y.val;
    } else if (isEmptySExp(x) && isEmptySExp(y)) {
        return true;
    } else if (isNumber(x) && isNumber(y)) {
        return x === y;
    } else if (isString(x) && isString(y)) {
        return x === y;
    } else if (isBoolean(x) && isBoolean(y)) {
        return x === y;
    } else {
        return false;
    }
};

const carPrim = (v: Value): Value | Error =>
    isCompoundSExp(v) ? v.val1 :
        Error(`Car: param is not compound ${v}`);

const cdrPrim = (v: Value): Value | Error =>
    isCompoundSExp(v) ? v.val2 :
        Error(`Cdr: param is not compound ${v}`);

const consPrim = (v1: Value, v2: Value): CompoundSExp =>
    makeCompoundSExp(v1, v2);

export const listPrim = (vals: Value[]): EmptySExp | CompoundSExp =>
    vals.length === 0 ? makeEmptySExp() :
        makeCompoundSExp(first(vals), listPrim(rest(vals)))

const isListPrim = (v: Value): boolean =>
    isEmptySExp(v) || isCompoundSExp(v);

const isPairPrim = (v: Value): boolean =>
    isCompoundSExp(v);

interface Tree {
    tag: "Tree",
    rootId: string,
    graph: Graph,
}

function handleClosureGraph(frameBinding: FBinding, resGraph:Graph, envName:string):void {
    let closure = unbox(frameBinding.val);
    if (isClosure(closure)) {
        // let new_closure = makeClosureBodyId(closure);
        // let currentBodyId:BodyId;
        // if(closure['bodyId']=== undefined){
        //     currentBodyId = generateBodyId();
        //     closure['bodyId'] = currentBodyId;
        // }else{
        //     currentBodyId = closure['bodyId'];
        // }
        let currentBodyId = closure.bodyId;
        let closureLabel = makeClosureLabel(currentBodyId, closure);
        resGraph.setNode(currentBodyId, {label: closureLabel, shape: "record", color: "white"});
        resGraph.setEdge(envName, currentBodyId, {tailport: frameBinding.var, headport: currentBodyId});
        resGraph.setEdge(currentBodyId, closure.env.id, {tailport: "0"});
    }
}

/*
* accepts a persistent environment and draws its diagram
* */
export const drawEnvDiagram = (pEnv: {}): Tree | Error => {
    let resGraph = new Graph();
    // add nodes
    Object.keys(pEnv).forEach((envName) => {
        let env = pEnv[envName];
        if (typeof env !== "undefined") {
            let label = makeLabel(envName, env);
            resGraph.setNode(envName, {label: label, shape: "Mrecord"});
            if (isGlobalEnv(env)) {
                let frame = unbox(env.frame);
                frame.fbindings
                    .forEach(frameBinding => {
                        handleClosureGraph(frameBinding, resGraph, envName);
                    });
            } else {
                if (isExtEnv(env)) {
                    let frame = env.frame;
                    if (isFrame(frame)) {
                        frame.fbindings
                            .forEach(frameBinding => {
                                handleClosureGraph(frameBinding, resGraph, envName);
                            });
                    }
                }
            }

        }
    });
    // //add edges
    Object.keys(pEnv).forEach(envName => {
        let currentEnv = pEnv[envName];
        if (isExtEnv(currentEnv)) {
            resGraph.setEdge(envName, currentEnv.env.id);
            makeReturnEnvLeaf(resGraph, currentEnv.returnEnv.id, currentEnv.id);
        }
    });
    return {tag: "Tree", rootId: "root", graph: resGraph};
};

const makeReturnEnvLeaf = (graph: Graph, envName: string, fromEnvName: string): void => {
    let nodeName = envName + "_link_" + fromEnvName;
    graph.setNode(nodeName, {label: envName, shape: "plaintext"});
    graph.setEdge(fromEnvName, nodeName, {style: "dashed"});
};

const bindingToString = (binding: FBinding): string => {
    if (isClosure(unbox(binding.val)))
        return "<" + binding.var + ">" + binding.var + ": ";
    else
        return binding.var + ":" + binding.val;
};

const makeClosureLabel = (bodyId: BodyId, closure: Closure): string => {
    return "{<" + bodyId + ">" + "◯◯\\l|p:" +
        closure.params.map(param => param.var).join(",") + "\\l| b: " +
        closure.body.map(unparse).join(" ") + "\\l}";
};

const makeLabel = (envName: string, env: Env): string => {
    let label = "{" + envName + "|";
    if (isGlobalEnv(env)) {
        label += unbox(env.frame).fbindings.map(bindingToString).join("\\l|");

    } else if (isExtEnv(env)) {
        if (isFrame(env.frame)) {
            label += env.frame.fbindings.map(bindingToString).join("\\l|");
        }
    }
    label += "\\l}";
    return label;
};
/*
* wrapper function for the whole process:
* it runs parseEval and then drawEnvDiagram
* */
export const evalParseDraw = (s: string): string | Error => {
    evalParse1(s);
    let tree = drawEnvDiagram(persistentEnv);
    if (isError(tree))
        return tree;
    else
        return dot.write(tree.graph);
};
// const demoProgStr: string = "(L4 (define z 4) (define foo (lambda (x y) (+ x y))) (foo 4 5) ((lambda (x) 5) 8))";
// const demoProgStr: string = "(L4 (define z 4) (define foo (lambda (x y) (+ x y))) (foo 4 5))";
// const demoProgStr: string = "(L4 (define make-adder (lambda (a) (lambda (x) (+ x a) ) ) ) (define a5 (make-adder 5)) (a5 10))";
// const demoProgStr: string = "(L4 (let ((f (let ((a 1))(lambda (x)(+ x a)))))(f 10)))";
const demoProgStr: string = "(L4 (define x (lambda (x) (* 2 x))) (define y (lambda (f) f)) (y x))";
console.log(evalParseDraw(demoProgStr));


// - no B0 in closure
// const test2=`
// (L4
//   (define z 4)
//   (define foo (lambda (x y) (+ x y)))
//   (foo 4 5))`;
// console.log(evalParseDraw(test2));


// empty GE env seen as spllited squre - should be squre
// const test4=`
// (L4
//   (let ((c 1) (d 1)) (+ c d)))`;
// console.log(evalParseDraw(test4));


// const test5=`
//   (L4
//     (define x
//       (lambda (x) (* 2 x)))
//     (define y
//       (lambda (f) f))
//     (y x))`;
// console.log(evalParseDraw(test5));

//
// const test6=`(L4 (define x (lambda (x) (* 2 x))) (define y (lambda (f) f)) (y x))`;
// console.log(evalParseDraw(test6));
//
//
// const test7 = "(L4 (define makeAdder (lambda (n) (lambda (y) (+ y n))))(define a6 (makeAdder 6))(define a7 (makeAdder 7))(+ (a6 1) (a7 1)))";
// console.log(evalParseDraw(test7));
//
//
// const test8=`(L4 (define z 4) (define foo (lambda (x y) (+ x y))) (foo 4 5))`;
// console.log(evalParseDraw(test8));
//
// const test9=`(L4(define fact(lambda (n)(if(= n 0) 1 (* n (fact (- n 1))))))(fact 3))`;
// console.log(evalParseDraw(test9));


