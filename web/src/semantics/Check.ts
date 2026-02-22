import { add, bind } from 'lodash';
import { printTerm } from '../lytr/print';
import type { Term } from '../lytr/term';
import { meta } from '../lytr/term';
import type { Error } from './Error';


type Proposition = Term
export type FullType = [Term[], Term]
export type Context = Map<string, FullType | null>
export type holeInfo = {goal : Proposition, context: Context}
type staticInfo = {errors: Error[], holes:[Number, holeInfo][], inferred: FullType | null, bindings:Context}

// function combineTermes(Term1 : Term, Term2 : Term) : Term {
//     return [...Term1, ...Term2];
// }

const Hole : Term = meta({type:"Hole", inserted:false})
const FullHole : FullType = [[], Hole]

function combineBindings(c1 : Context, c2 : Context) : Context {
    var c : Context = new Map(c1); 
    c2.forEach((v, k) => c.set(k, v));
    return c
}

function combineInfos(infos : staticInfo[]) : staticInfo {
    if (infos.length === 0) {
        return {errors: [], holes: [], inferred: null, bindings: new Map()}
    } if (infos.length === 1) {
        return infos[0]
    } 
    const [info1, info2,...rest] = infos;
    const info : staticInfo = {
        errors: [...info1.errors,... info2.errors], 
        holes: [...info1.holes,... info2.holes], 
        inferred:null,
        bindings: combineBindings(info1.bindings, info2.bindings)
    }
    return combineInfos([info,...rest])
}

function addErrors(info : staticInfo, errors : Error[]) : staticInfo {
    return {...info, errors: [...info.errors,...errors]}
}

function addBindings(info : staticInfo, bindings : Context) : staticInfo {
    return {...info, bindings: combineBindings(info.bindings, bindings)}
}

type CheckingMode = 
    {type: "program"}
    | {type: "line"}
    | {type: "spine"}
    | {type: "argument"}
    | {type: "identifier"}
    | {type: "expression", expected: Term | null}


// function matchConjuction(t : Term | null) : {valid:boolean, sides:[Term | null, Term | null]} {
//     if(!t) {
//         return {valid:true, sides:[null, null]} 
//     }
//     if(t.value.type === "Hole") {
//         return {valid:true, sides:[Hole, Hole]}
//     } else if(t.value.type === "InfixBinop" && t.value.binop.type === "And") {
//         return {valid:true, sides:[t.value.left,t.value.right]}
//     } else {
//         return {valid:false, sides:[Hole, Hole]}
//     }
// }

// function matchImplication(t : Term | null) : {valid:boolean, sides:[Term | null, Term | null]} {
//     if(!t) {
//         return {valid:true, sides:[null, null]} 
//     }
//     if(t.value.type === "Hole") {
//         return {valid:true, sides:[Hole, Hole]}
//     } else if(t.value.type === "InfixBinop" && t.value.binop.type === "Arrow") {
//         return {valid:true, sides:[t.value.left,t.value.right]}
//     } else {
//         return {valid:false, sides:[Hole, Hole]}
//     }
// }


// function matchDisjunction(t : Term | null) : {valid:boolean, sides:[Term | null, Term | null]} {
//     if(!t) {
//         return {valid:true, sides:[null, null]} 
//     }
//     if(t.value.type === "Hole") {
//         return {valid:true, sides:[Hole, Hole]}
//     } else if(t.value.type === "InfixBinop" && t.value.binop.type === "Or") {
//         return {valid:true, sides:[t.value.left,t.value.right]}
//     } else {
//         return {valid:false, sides:[Hole, Hole]}
//     }
// }

function combine(ts1 : Term | null, ts2 : Term | null) : {valid:boolean, combination: Term | null} {
    if(!ts1 || !ts2) {
        return {valid:true, combination: null}
    }
    if((ts1.value.type === "Hole") || (ts2.value.type === "Hole")){
        return {valid:true, combination: Hole}
    }
    if(ts1.value.type !== ts2.value.type) {
        return {valid:false, combination: Hole}
    }
    if(ts1.value.type === "Identifier" && ts2.value.type === "Identifier" && ts1.value.value === ts2.value.value) {
        return {valid:true, combination: ts1} 
    }
    // TODO: more cases :(
    return {valid:false, combination: Hole}
}

function inCtx(ctx: Context, x : string) : {valid:boolean, inferred:FullType|null} {
    if (x == "U") {
        return {valid : true, inferred:null}
    }
    const infer = ctx.get(x);
    if (infer) {
        return {valid:true, inferred:infer}
    }
    return {valid:false, inferred:[[],Hole]}
}

function subsume(mode:CheckingMode, from : number, to:number, inferred:FullType|null, errors:Error[]) : Error[] {
    if(mode.type === "expression") {
        // console.log("sus exp", mode.expected)
        if (inferred && inferred[0].length > 0 && mode.expected) {
            var error = {type: "mark", message: "Too few arguments", from, to }
            return [error]
        }
        var inferred_out = inferred ? inferred[1] : null;
        var consitent = combine(mode.expected, inferred_out).valid
        if (!consitent && mode.expected && inferred_out) {
            var error = {type: "mark", message: 'Inconsitency (expected ' + printTerm(mode.expected) + ", got " + printTerm(inferred_out) + ")", from, to }
            errors = [error, ...errors]
        }
    }
    return errors
}

function countArgs(argsExpected : number, argsFound : number, from : number, to:number, errors:Error[]) : Error[] {
    if (argsExpected == argsFound) { return errors }
    var error = {type: "mark", message: (argsExpected > argsFound ? "Too few arguments" : "Too many arguments"), from, to }
    errors = [error, ...errors]
    return errors
}

// function partiallyApplied(x:String, from : number, to:number, errors:Error[]) : Error[] {
//     var error = {type: "mark", message: "Not fully applied", from, to }
//     errors = [error, ...errors]
//     return errors
// }

// function ensureArg(mode:CheckingMode, from : number, to:number, errors:Error[]) : Error[] {
//     if (mode.type !== "argument") {
//         var error = {type: "mark", message: 'Ascription found where ' + mode.type + " expected", from, to }
//         errors = [error, ...errors]
//     }
//     return errors
// }

// function ensureProgram(mode:CheckingMode, from : number, to:number, errors:Error[]) : Error[] {
//     if (mode.type !== "program") {
//         var error = {type: "mark", message: 'Program found where ' + mode.type + " expected", from, to }
//         errors = [error, ...errors]
//     }
//     return errors
// }

// function ensureExp(mode:CheckingMode, from : number, to:number, errors:Error[]) : Error[] {
//     if (mode.type !== "expression") {
//         var error = {type: "mark", message: 'Expression found where ' + mode.type + " expected", from, to }
//         errors = [error, ...errors]
//     }
//     return errors
// }

function ensureMode(allowed : string[], mode:CheckingMode, from : number, to:number, errors:Error[]) : Error[] {
    if (!allowed.includes(mode.type)) {
        var error = {type: "mark", message: 'Sort error (expected '+mode.type+", found "+allowed+")", from, to }
        errors = [error, ...errors]
    }
    return errors
}

// function ensureExpected(mode:CheckingMode, from : number, to:number, errors:Error[]) {
//     if (mode.type === "expression" && !mode.expected) {
//         var error = {type: "mark", message: "Inference failure", from, to }
//         errors = [error, ...errors]
//     }
//     return errors
// }

function checkTerm(ctx : Context, mode: CheckingMode, t: Term): staticInfo {
    switch (t.value.type) {
        case 'Postulate' : {
            var infos = combineInfos([]);
            for (const line of t.value.body) {
                const info = checkTerm(ctx, {type: "line"}, line)
                infos = combineInfos([infos, info]);
                ctx = combineBindings(ctx, info.bindings);
            }
            infos = addBindings(infos, ctx)

            var errors = ensureMode(["program"], mode, t.meta.start, t.meta.end, [])
            return addErrors(infos, errors)
        }
        case 'Identifier' : {
            var inferred  : FullType | null = null;
            errors = ensureMode(["expression", "spine", "identifier"], mode, t.meta.start, t.meta.end, [])
            if(mode.type == "expression") {
                var inctx = inCtx(ctx, t.value.value)
                var errors : Error[] = []
                if (!inctx.valid) {
                    var error = {type: "mark", message: 'Unbound variable ' + t.value.value, from: t.meta.start, to: t.meta.end }
                    errors = [error, ...errors]
                }
                var inferred : FullType | null = inctx.inferred
                console.log(t.value.value, inferred)
                if(inferred) {
                    errors = subsume(mode, t.meta.start, t.meta.end, inferred, errors)
                }
                // if(inferred && inferred[0].length > 0) {
                //     errors = partiallyApplied(t.value.value, t.meta.start, t.meta.end, errors)
                // }
            }
            return  {errors, holes:[], inferred, bindings:new Map()} 
        }
        case 'Asc' : {
            if (mode.type == "line") {
                // var original_ctx = new Map(ctx)
                infos = checkTerm(ctx, {type: "spine"}, t.value.left)
                infos = combineInfos([infos, checkTerm(combineBindings(ctx, infos.bindings), {type: "expression", expected: Hole}, t.value.right)]);
                // infos.bindings = original_ctx
                if (t.value.left.value.type == "Identifier") {
                    var x : string = t.value.left.value.value;
                    var y : FullType = [[], t.value.right];
                    infos.bindings = new Map([[x, y]])
                }
                else if (t.value.left.value.type == "Ap" && t.value.left.value.fun.value.type == "Identifier") {
                    var x : string = t.value.left.value.fun.value.value;
                    var y : FullType = [t.value.left.value.args, t.value.right];
                    infos.bindings = new Map([[x, y]])
                } 
                return infos
            } else if (mode.type == "argument") {
                var leftInfo = checkTerm(ctx, {type: "identifier"}, t.value.left);
                var rightInfo = checkTerm(ctx, {type: "expression", expected: Hole}, t.value.right);
                infos = combineInfos([leftInfo, rightInfo]);
                if (leftInfo.errors.length == 0 && t.value.left.value.type == "Identifier") {
                    var x : string = t.value.left.value.value;
                    var y : FullType = [[], t.value.right];
                    infos = addBindings(infos, new Map([[x, y]]))
                }
                return infos
            }
            errors = ensureMode(["argument"], mode, t.meta.start, t.meta.end, [])
            infos = combineInfos([checkTerm(ctx, {type: "expression", expected: Hole}, t.value.left), checkTerm(ctx, {type: "expression", expected: Hole}, t.value.right)]);
            return addErrors(infos, errors)
        }
        case 'Ap' : {
            errors = []
            if (mode.type == "spine") {
                infos = checkTerm(ctx, {type: "identifier"}, t.value.fun)
                var ctx = combineBindings(ctx, infos.bindings);
                for (const arg of t.value.args) {
                    infos = combineInfos([infos, checkTerm(ctx, {type: "argument"}, arg)]);
                    ctx = combineBindings(ctx, infos.bindings);
                }
                return infos
            } else if (mode.type == "expression") {
                infos = checkTerm(ctx, {type: "expression", expected:null}, t.value.fun)
                var funtype = infos.inferred
                if (funtype){
                    errors = countArgs(funtype[0].length, t.value.args.length, t.value.fun.meta.start, t.value.fun.meta.end, errors)
                }
                infos = combineInfos([infos,... t.value.args.map(c => checkTerm(ctx, {type: "expression", expected:Hole}, c))]);
                infos = addErrors(infos, errors)
                return infos
            }
            errors = ensureMode(["spine"], mode, t.meta.start, t.meta.end, errors)
            infos = checkTerm(ctx, {type: "expression", expected:Hole}, t.value.fun)
            infos = combineInfos([infos,... t.value.args.map(c => checkTerm(ctx, {type: "expression", expected:Hole}, c))]);
            return addErrors(infos, errors)
        }
        case 'Hole': {
            if (mode.type === "expression") {
                var expected : Term | null = mode.expected ? mode.expected : Hole
                var holes : [Number, holeInfo][] = [[t.meta.start, {goal:expected, context:ctx}]];
                return {errors:[], holes:holes, inferred:FullHole, bindings: new Map() } 
            }
            var error = {type: "mark", message: 'Hole in non-expression', from: t.meta.start, to: t.meta.end }
            return {errors:[error], holes:[], inferred:FullHole, bindings: new Map()  } 
        }
        default: {
            console.log(t);
        }
        // case 'Theorem': {
        //     var infos = combineInfos([
        //         checkTerm(ctx, {type : "identifier"}, t.value.pat), 
        //         checkTerm(ctx, {type : "proposition"}, t.value.prop), 
        //         checkTerm(ctx, {type : "proof", expected: t.value.prop}, t.value.body)])
        //     var errors : Error[] = [];
        //     if (mode.type !== "program") {
        //         var error = {type: "mark", message: 'Theorem found where ' + mode.type + " expected", from: t.meta.start, to: t.meta.end }
        //         errors = [error, ...errors]
        //     }
        //     return addErrors(infos, errors) 
        // }
        // case 'Pair': {
        //     var errors : Error[] = [];
        //     var expecteds : [Term | null, Term | null] = [null, null]
        //     if (mode.type === "proof") {
        //         var match = matchConjuction(mode.expected);
        //         expecteds[0] = match.sides[0]
        //         expecteds[1] = match.sides[1]
        //         if (!match.valid) {
        //             var error = {type: "mark", message: 'Proof of non-conjunction expected', from: t.meta.start, to: t.meta.end }
        //             errors = [error, ...errors]
        //         }
        //     } 
        //     errors = ensureExp(mode, t.meta.start, t.meta.end, errors)
        //     var check1 = checkTerm(ctx, {type:"proof", expected:expecteds[0]}, t.value.left)
        //     var check2 = checkTerm(ctx, {type:"proof", expected:expecteds[1]}, t.value.right)

        //     var infos = combineInfos([check1, check2])

        //     var inferred : Term | null = null 
        //     if(check1.inferred && check2.inferred) {
        //         inferred = meta({type:"Pair", left:check1.inferred, right:check2.inferred})
        //     }   

        //     return {...addErrors(infos, errors),...inferred}
        // }
        // case 'Hole': {
        //     if (mode.type === "proof") {
        //         var expected : Term | null = mode.expected ? mode.expected : Hole
        //         var holes : [Number, holeInfo][] = [[t.meta.start, {goal:expected, context:ctx}]];
        //         return {errors:[], holes:holes, inferred:Hole } 
        //     }
        //     var error = {type: "mark", message: 'Hole in non-proof', from: t.meta.start, to: t.meta.end }
        //     return {errors:[error], holes:[], inferred:Hole } 
        // }
        // case 'Numlit': {
        //     var error = {type: "mark", message: 'Numbers not supported', from: t.meta.start, to: t.meta.end }
        //     return {errors:[error], holes:[], inferred:Hole } 
        // }
        // case 'InfixBinop': {
        //     switch (t.value.binop.type) {
        //         case 'Arrow': {
        //             var infos = combineInfos([
        //                 checkTerm(ctx, {type : "proposition"}, t.value.left), 
        //                 checkTerm(ctx, {type : "proposition"}, t.value.right)])
        //             var errors : Error[] = []
        //             if (mode.type !== "proposition") {
        //                 var error = {type: "mark", message: 'Implication found where ' + mode.type + " expected", from: t.meta.start, to: t.meta.end }
        //                 errors = [error, ...errors]
        //             }
        //             return addErrors(infos, errors) 
        //         }
        //         case 'And': {
        //             var infos = combineInfos([
        //                 checkTerm(ctx, {type : "proposition"}, t.value.left), 
        //                 checkTerm(ctx, {type : "proposition"}, t.value.right)])
        //             var errors : Error[] = []
        //             if (mode.type !== "proposition") {
        //                 var error = {type: "mark", message: 'Conjunction found where ' + mode.type + " expected", from: t.meta.start, to: t.meta.end }
        //                 errors = [error, ...errors]
        //             }
        //             return addErrors(infos, errors) 
        //         }
        //         case 'Or': {
        //             var infos = combineInfos([
        //                 checkTerm(ctx, {type : "proposition"}, t.value.left), 
        //                 checkTerm(ctx, {type : "proposition"}, t.value.right)])
        //             var errors : Error[] = []
        //             if (mode.type !== "proposition") {
        //                 var error = {type: "mark", message: 'Disjunction found where ' + mode.type + " expected", from: t.meta.start, to: t.meta.end }
        //                 errors = [error, ...errors]
        //             }
        //             return addErrors(infos, errors)
        //         }
        //         case 'Fun': {
        //             var errors : Error[] = [];
        //             var expected1 : Term | null = null;
        //             var expected2 : Term | null = null;
        //             if (mode.type === "proof") {
        //                 var match = matchImplication(mode.expected);
        //                 expected1 = match.sides[0]
        //                 expected2 = match.sides[1]
        //                 if (!match.valid) {
        //                     var error = {type: "mark", message: 'Proof of non-implication expected', from: t.meta.start, to: t.meta.end }
        //                     errors = [error, ...errors]
        //                 }
        //                 errors = ensureExpected(mode, t.meta.start, t.meta.end, errors)
        //             } 
        //             errors = ensureExp(mode, t.meta.start, t.meta.end, errors)
        //             var newCtx : Context = t.value.left.value.type === "Identifier" ? new Map([...ctx, [t.value.left.value.value, expected1 || Hole]]) : ctx; 
        //             var info = combineInfos([
        //                 checkTerm(ctx, {type : "identifier"}, t.value.left), 
        //                 checkTerm(newCtx, {type : "proof", expected: expected2}, t.value.right)])
        //             return {...addErrors(info, errors), inferred:null}
        //         }
        //     }
        // }
        // case 'Ap': {
        //     var errors : Error[] = [];
        //     var infer = checkTerm(ctx, {type:"proof", expected:null}, t.value.fun)
        //     var match = matchImplication(infer.inferred);
        //     var check = checkTerm(ctx, {type:"proof", expected:match.sides[0]}, t.value.arg)
        //     var inferred = match.sides[1]
        //     var info = combineInfos([infer, check])
        //     if (!match.valid) {
        //         var error = {type: "mark", message: 'Cannot apply non-implication', from: t.meta.start, to: t.meta.end }
        //         errors = [error, ...errors]
        //     }
        //     errors = subsume(mode, t.meta.start, t.meta.end, inferred, errors)
        //     errors = ensureExp(mode, t.meta.start, t.meta.end, errors)
        //     return {...addErrors(info, errors),inferred}
        // }
        // case 'PrefixUnop': {
        //     switch(t.value.unop.type) {
        //         case "L": {
        //             var errors : Error[] = [];
        //             var expected : Term | null = null;
        //             if(mode.type === "proof") {
        //                 var match = matchDisjunction(mode.expected);
        //                 expected = match.sides[0]
        //                 if (!match.valid) {
        //                     var error = {type: "mark", message: 'Non-disjunction expected', from: t.meta.start, to: t.meta.end }
        //                     errors = [error, ...errors]
        //                 }
        //             }
        //             var check = checkTerm(ctx, {type:"proof", expected}, t.value.right)
        //             errors = ensureExpected(mode, t.meta.start, t.meta.end, errors)
        //             errors = ensureExp(mode, t.meta.start, t.meta.end, errors)
        //             return {...addErrors(check, errors), inferred:null}
        //         }
        //         case "R": {
        //             var errors : Error[] = [];
        //             var expected : Term | null = null;
        //             if(mode.type === "proof") {
        //                 var match = matchDisjunction(mode.expected);
        //                 expected = match.sides[1]
        //                 if (!match.valid) {
        //                     var error = {type: "mark", message: 'Non-disjunction expected', from: t.meta.start, to: t.meta.end }
        //                     errors = [error, ...errors]
        //                 }
        //             }
        //             var check = checkTerm(ctx, {type:"proof", expected}, t.value.right)
        //             errors = ensureExpected(mode, t.meta.start, t.meta.end, errors)
        //             errors = ensureExp(mode, t.meta.start, t.meta.end, errors)
        //             return {...addErrors(check, errors), inferred:null}
        //         }
        //     }
        //     break;
        // }
        // case 'PostfixUnop': {
        //     switch(t.value.unop.type) {
        //         case "Fst": {
        //             var errors : Error[] = [];
        //             var infer = checkTerm(ctx, {type:"proof", expected:null}, t.value.left)
        //             var match = matchConjuction(infer.inferred);
        //             var inferred = match.sides[0]
        //             if (!match.valid) {
        //                 var error = {type: "mark", message: 'Cannot access entry of non-conjunction', from: t.meta.start, to: t.meta.end }
        //                 errors = [error, ...errors]
        //             }
        //             errors = subsume(mode, t.meta.start, t.meta.end, inferred, errors)
        //             errors = ensureExp(mode, t.meta.start, t.meta.end, errors)
        //             return {...addErrors(infer, errors),inferred}
        //         }
        //         case "Snd": {
        //             var errors : Error[] = [];
        //             var infer = checkTerm(ctx, {type:"proof", expected:null}, t.value.left)
        //             var match = matchConjuction(infer.inferred);
        //             var inferred = match.sides[1]
        //             if (!match.valid) {
        //                 var error = {type: "mark", message: 'Cannot access entry of non-conjunction', from: t.meta.start, to: t.meta.end }
        //                 errors = [error, ...errors]
        //             }
        //             errors = subsume(mode, t.meta.start, t.meta.end, inferred, errors)
        //             errors = ensureExp(mode, t.meta.start, t.meta.end, errors)
        //             return {...addErrors(infer, errors),inferred}
        //         }
        //     }
        //     break;
        // }
        // case 'Case': {
        //     var errors : Error[] = [];
        //     var info : staticInfo = combineInfos([]);
        //     var inferred : Term | null = null
        //     var infer = checkTerm(ctx, {type:"proof", expected:null}, t.value.scrutinee)
        //     var info = infer
        //     var match = matchDisjunction(infer.inferred)
        //     if (!match.valid) {
        //         var error = {type: "mark", message: 'Cannot case on non-disjunction', from: t.meta.start, to: t.meta.end }
        //         errors = [error, ...errors]
        //     }

        //     var expected : Term | null = null 
        //     if(mode.type === "proof") {
        //         expected = mode.expected
        //     } 
        //     errors = ensureExp(mode, t.meta.start, t.meta.end, errors)

        //     if(t.value.cases.length < 1) {
        //         var error = {type: "mark", message: 'Empty case proof', from: t.meta.start, to: t.meta.end }
        //         errors = [error, ...errors]
        //     } else {
        //         // var infer1 = checkTerm(ctx, {type:"proof", expected:null}, t.value.cases[0][0])
        //         var ctx1 : Context = ctx 
        //         if( match.sides[0] && t.value.cases[0][0].value.type === "PrefixUnop" && t.value.cases[0][0].value.unop.type === "L" && t.value.cases[0][0].value.right.value.type === "Identifier") {
        //             ctx1 = new Map([...ctx, [t.value.cases[0][0].value.right.value.value, match.sides[0]]])
        //         } else {
        //             var error = {type: "mark", message: 'Ill-formed case', from: t.meta.start, to: t.meta.end }
        //             errors = [error, ...errors]
        //         }
        //         var check1 = checkTerm(ctx1, {type:"proof", expected}, t.value.cases[0][1])
        //         info = combineInfos([info,check1])
        //         if (t.value.cases.length < 2) {
        //             var error = {type: "mark", message: 'Missing second case', from: t.meta.start, to: t.meta.end }
        //             errors = [error, ...errors]
        //             inferred = !expected ? check1.inferred : null
        //         } else {
        //             var ctx2 : Context = ctx 
        //             if( match.sides[1] && t.value.cases[1][0].value.type === "PrefixUnop" && t.value.cases[1][0].value.unop.type === "R" && t.value.cases[1][0].value.right.value.type === "Identifier") {
        //                 ctx2 = new Map([...ctx, [t.value.cases[1][0].value.right.value.value, match.sides[1]]])
        //             } else {
        //                 var error = {type: "mark", message: 'Ill-formed case', from: t.meta.start, to: t.meta.end }
        //                 errors = [error, ...errors]
        //             }
        //             // var infer2 = checkTerm(ctx, {type:"proof", expected:null}, t.value.cases[1][0])
        //             var check2 = checkTerm(ctx2, {type:"proof", expected}, t.value.cases[1][1])
        //             info = combineInfos([info,check2])
        //             if (!expected) {
        //                 var combination = combine(check1.inferred, check2.inferred)
        //                 inferred = combination.combination
        //                 if(!combination.valid) {
        //                     var error = {type: "mark", message: 'Inconsistent branches', from: t.meta.start, to: t.meta.end }
        //                     errors = [error, ...errors]
        //                 }
        //             }
        //         }
        //     }
        //     return {...addErrors(info, errors), inferred} 
        // }
        // case 'BUILDER ERROR': {
        //     return {errors:[{type:"build", message:"BUILDER ERROR", from:0, to:0}], holes:[], inferred:Hole } 
        // }
    }
    return combineInfos([]);
}

export function getStatics(Term: Term): staticInfo {
    return checkTerm(new Map(), {type: 'program'}, Term)
}