import { Graph } from "graphlib";
import dot = require("graphlib-dot");
import { length, map, range, zipWith } from "ramda";
import {
    AtomicExp,
    Exp,
    IfExp,
    Parsed,
    VarDecl,
    isAtomicExp,
    DefineExp,
    AppExp,
    ProcExp,
    isAppExp,
    isDefineExp,
    isExp,
    isIfExp,
    isProcExp,
    parse,
    unparse,
    isProgram,
    isBoolExp,
    isNumExp,
    isStrExp,
    isLitExp,
    isVarRef,
    isPrimOp,
    isLetExp,
    isLetrecExp,
    isSetExp,
    LitExp,
    PrimOp,
    VarRef,
    LetExp,
    Binding,
    makeVarDecl,
    Program,
    CExp, isCExp, LetrecExp, SetExp, CompoundExp, StrExp
} from "./L4-ast";
import {safeF2, safeFL, safeF, isError} from "./error";
import {
    Closure,
    CompoundSExp,
    EmptySExp,
    isCompoundSExp,
    isEmptySExp, makeEmptySExp,
    SExp,
    SymbolSExp,
    valueToString
} from "./L4-value";
import {isNumber} from "./list";

const generateId = () => '_' + Math.random().toString(36).substr(2, 9);

interface Tree {
    tag: "Tree",
    rootId: string,
    graph: Graph,
}

export const isTree = (x: any): x is Tree => x.tag === "Tree";

const makeLeaf = (label: string): Tree => {
    let graph = new Graph();
    const headId = generateId();
    graph.setNode(headId, { label, shape: "record" });
    return { tag: "Tree", rootId: headId, graph };
};


const makeTree = (label: string, nodes: Tree[], edgesLabels: string[]): Tree => {
    let graph = new Graph();
    const headId = generateId();
    graph.setNode(headId, { label, shape: "record" });
    zipWith(
        (t, edgeLabel) => {
            map(n => graph.setNode(n, t.graph.node(n)), t.graph.nodes());
            map(e => graph.setEdge(e.v, e.w, t.graph.edge(e)), t.graph.edges());
            graph.setEdge(headId, t.rootId, {label: edgeLabel});
        },
        nodes,
        edgesLabels
    );
    return { tag: "Tree", rootId: headId, graph };
};

const astToDot = (ast: Tree): string => dot.write(ast.graph);

const expToTree = (exp: string) =>
    safeF(astToDot)(safeF(makeAST)(parse(exp)));

const makeLitExpTree = (exp: LitExp): Tree | Error => {
    if (isCompoundSExp(exp.val)){
        const compoundTree = makeCompundSexpTree(exp.val);
        if (isError(compoundTree)){
            return compoundTree
        }else {
            return makeTree(exp.tag,  [compoundTree],  ["val"]);
        }
    } else {
        return makeSexpLeaf(exp.val);
    }
};

const makeCompundSexpTree = (exp: CompoundSExp): Tree | Error => {
    const leaf1 = makeSexpLeaf(exp.val1);
    if (isError(leaf1)){
        return leaf1;
    } else {
        if (isEmptySExp(exp.val2)) { // last in the list

            if (isError(leaf1)){
                return leaf1;
            } else {
                const leaf2 = makeEmptySexpLeaf();
                return makeTree(exp.tag, [leaf1, leaf2], ["val1", "val2"]);
            }
        } else {
            if (isCompoundSExp(exp.val2)){
                const leaf2 = makeCompundSexpTree(exp.val2);
                if (isError(leaf2)){
                    return leaf2;
                } else {
                    return makeTree(exp.tag, [leaf1, leaf2], ["val1", "val2"]);
                }
            } else {
                return Error(`makeCompundSexpTree: cant make compound chain, val2 is ${exp.val2}`);
            }

        }
    }
};

const makeEmptySexpLeaf = (): Tree =>
    makeLeaf(makeEmptySExp().tag);

const makeSexpLeaf = (sexp: SExp): Tree | Error => {
    return isNumber(sexp)? makeLeaf(sexp.toString()) : makeLeaf(sexp.toString());
    // number | boolean | string | PrimOp | Closure | SymbolSExp | EmptySExp | CompoundSExp
};

const makeVarRefTree = (exp: VarRef): Tree =>
    makeTree(exp.tag, [makeLeaf(exp.var)], ["var"]);


const makeVarDeclTree = (exp: VarDecl): Tree =>
    makeTree(exp.tag, [makeLeaf(exp.var)], ["var"]);


const makeProcExpTree = (exp: ProcExp): Tree | Error => {
    const argsTrees = exp.args.map(makeVarDeclTree);
    const bodyTrees = exp.body.map(makeCExpTree);
    if (bodyTrees.some(isError)){
        return bodyTrees.filter(isError)[0];
    } else {
        const argsNode = makeListNode(argsTrees);
        // @ts-ignore -> ts thinks that bodyTrees is of type Tree|Error[] ,  when its really Tree[]
        const bodyNode = makeListNode(bodyTrees);
        return makeTree(exp.tag, [argsNode, bodyNode], ["args", "body"]);
    }
};

const makeIfExpTree = (exp: IfExp): Tree | Error => {
    const test = makeCExpTree(exp.test);
    const then = makeCExpTree(exp.then);
    const alt = makeCExpTree(exp.alt);
    if (isError(test)){
        return test;
    } else if (isError(then)){
        return then;
    } else if (isError(alt)){
        return alt;
    } else
        return makeTree(exp.tag, [test, then, alt], ["test", "then", "alt"]);
};

const makeAppExpTree = (exp: AppExp): Tree | Error =>{
    const rator = makeCExpTree(exp.rator);
    if (isError(rator)){
        return rator;
    } else {
        const rands = exp.rands.map(makeCExpTree);
        if (rands.some(isError)){
            return rands.filter(isError)[0];
        } else {
            // @ts-ignore -> ts thinks that rands is of type (Tree | Error)[] ,  when its really Tree[]
            return makeTree(exp.tag, [rator, makeListNode(rands)], ["rator", "rands"]);
        }
    }
};

const makeBindingTree = (exp: Binding): Tree | Error =>{
    const value = makeCExpTree(exp.val);
    if (isError(value)){
        return value;
    } else {
        return makeTree(exp.tag, [makeVarDeclTree(exp.var), value], ["var", "val"]);
    }
};

const makeLetTree = (exp: LetExp): Tree | Error => {
    const body = exp.body.map(makeCExpTree);
    if (body.some(isError)){
        return body.filter(isError)[0]
    } else{
        const bindings = exp.bindings.map(makeBindingTree);
        if (bindings.some(isError)){
            return bindings.filter(isError)[0]
        } else {
            // @ts-ignore -> ts thinks that (bindings, body) is of type (Tree | Error)[] ,  when its really Tree[]
            return makeTree(exp.tag, [makeListNode(bindings), makeListNode(body)], ["bindings", "body"])
        }
    }
};

const makeDefineTree = (exp: DefineExp): Tree | Error => {
    const valueNode = makeCExpTree(exp.val);
    if (isError(valueNode)){
        return valueNode;
    } else {
        return makeTree(exp.tag, [makeVarDeclTree(exp.var), valueNode], ["var", "val"]);
    }
};

const makeProgramTree = (exp: Program): Tree | Error => {
    const expressions = exp.exps.map(makeExpTree);
    if (expressions.some(isError)){
        return expressions.filter(isError)[0]
    } else{
        // @ts-ignore -> ts thinks that expressions is of type (Tree | Error)[] ,  when its really Tree[]
        return makeTree(exp.tag, [makeListNode(expressions)], ["exps"]);
    }
};

const makeListNode = (trees: Tree[]): Tree => {
    let a = trees;
    let b = trees.length;
    let c = range(0, trees.length);
    let f = 1;
    let d = range(0, trees.length).map(String);
    return makeTree(":", a, d)
};


export const makeAST = (exp: Parsed): Tree | Error =>
    isProgram(exp) ?  makeProgramTree(exp) :
    makeExpTree(exp);


const makeExpTree = (exp: Exp): Tree | Error =>
    isDefineExp(exp) ? makeDefineTree(exp) :
    makeCExpTree(exp);

const makeStrTree = (exp: StrExp): Tree =>{
    let l = makeLeaf(exp.val);
    return makeTree(exp.tag, [l], ["val"]);
};

const makeCExpTree = (exp: CExp): Tree | Error =>
    isLetrecExp(exp) || isSetExp(exp)? Error(`not supported: ${exp.tag}`):
    isNumExp(exp) ? makeTree(exp.tag, [makeLeaf(exp.val.toString())], ["val"]) :
    isBoolExp(exp) ? makeLeaf(exp.val? "true" : "false") :
    isStrExp(exp) ? makeStrTree(exp):
    isPrimOp(exp) ? makeTree(exp.tag, [makeLeaf(exp.op)], ["val"]) :
    isVarRef(exp) ? makeVarRefTree(exp):
    isAppExp(exp) ? makeAppExpTree(exp) :
    isIfExp(exp) ? makeIfExpTree(exp) :
    isProcExp(exp) ? makeProcExpTree(exp) :
    isLetExp(exp) ? makeLetTree(exp) :
    makeLitExpTree(exp);


const do1 = (p1:string)=>{
    console.log(p1);
    console.log(expToTree(p1));
    console.log("");

};

let programs = [
    "(define x 'hi)"
    // "(lambda (x y) x)",
    // "(lambda (x y) (+ x y z 5))",
    // "((lambda (x y) (+ x y z 5)) 8 9)",
    // "(L4 (define hi 'hi) (let ((x 1) (y 2)) (+ x y)))",
];
programs.map(do1);
// const p1 = "(+ x 4)";
// console.log(p1);
// console.log(expToTree(p1));
// console.log("");
//
// const p12 = "(define my-list '(1 2))";
// console.log(p12);
// console.log(expToTree(p12));
// console.log("");
//
// const p13 = "(define x 4)";
// console.log(p13);
// console.log(expToTree(p13));
// console.log("");
//
// const p2 = "(define y (+ x 4))";
// console.log(p2);
// console.log(expToTree(p2));
// console.log("");
//
// const p3 = "(if #t (+ x 4) 6)";
// console.log(p3);
// console.log(expToTree(p3));
// console.log("");
//
// const p4 = "(lambda (x y) x)";
// console.log(p4);
// console.log(expToTree(p4));
// console.log("");
