open Term;
open Error;
open MLType;
let _ = Print.printTerm; /* ensure Print is linked */

module StringMap = Map.Make(String);

type fullType = (list((option(string), term)), term);

type binding =
  | OL(option(fullType))
  | ML(mlType)
  | Builtin(string)        /* polymorphic builtin — name identifies the typing rule */
  | SchemaBinding(term)    /* unevaluated schema body, stored for Construct to evaluate */
  | MetaLet(term, mlType); /* unevaluated let body + inferred type, for schema evaluation */

type context = StringMap.t(binding);

type holeInfo = {
  goal: term,
  context,
};

type staticInfo = {
  errors: list(error),
  holes: list((int, holeInfo)),
  inferred: option(fullType),
  bindings: context,
};

let hole: term = mk(Hole(false));
let fullHole: fullType = ([], hole);

let emptyInfo = {errors: [], holes: [], inferred: None, bindings: StringMap.empty};

/* MetaLet definitions in definition order, for eval env construction.
   Set by Meta block processing, read by Construct block. */
let metaDefsRef: ref(list((string, term))) = ref([]);

let mergeBindings = (c1: context, c2: context): context =>
  StringMap.union((_key, _v1, v2) => Some(v2), c1, c2);

let mergeInfos = (i1: staticInfo, i2: staticInfo): staticInfo => {
  errors: i1.errors @ i2.errors,
  holes: i1.holes @ i2.holes,
  inferred: None,
  bindings: mergeBindings(i1.bindings, i2.bindings),
};

let withErrors = (info, errs) => {...info, errors: info.errors @ errs};
let withBindings = (info, ctx) => {...info, bindings: mergeBindings(info.bindings, ctx)};

/* --- Term resolution against an environment --- */

type env = StringMap.t(term);
let emptyEnv: env = StringMap.empty;

/* Witness substitution: maps names to (param_names, witness_body).
   For parameterless decls, param_names is [].
   For (f (x:A)) with witness w, resolving (f arg) gives w[x:=arg]. */
type witnessEnv = StringMap.t((list(string), term));
let emptyWitnessEnv: witnessEnv = StringMap.empty;

/* TODO: Implement resolve.
   Substitute identifiers in term t according to environment env.
   If env is empty, return t unchanged.
   For Identifier(v): look up v in env, return replacement if found.
   Recurse into all compound term variants: Asc, Ap, Postulate, Meta,
   Construct, Arrow, Eq, Comma, BinOp, List, Cons, Fun, Match, Let, If.
   Leave StringLit, Hole, Shard, BuilderError unchanged. */
let rec resolve = (_env: env, _t: term): term =>
  failwith("TODO")

/* TODO: Implement resolveWithParams.
   Like resolve but for witness substitution with parameterized declarations.
   If wenv is empty, return t unchanged.
   For Identifier(v): look up in wenv; if found with empty params, return witness directly.
   For Ap(Identifier(v), args): look up v in wenv; if found with params and matching arity,
     resolve args recursively, build a param->arg env, and resolve the witness with that env.
   Recurse into all other compound variants.
   Leave StringLit, Hole, Shard, BuilderError unchanged. */
and resolveWithParams = (_wenv: witnessEnv, _t: term): term =>
  failwith("TODO");

/* --- Checking modes --- */

type checkingMode =
  | Program
  | Line
  | Spine
  | Argument
  | IdentifierMode
  | Expression(option(term));

let stringOfMode =
  fun
  | Program => "program"
  | Line => "line"
  | Spine => "spine"
  | Argument => "argument"
  | IdentifierMode => "identifier"
  | Expression(_) => "expression";

/* --- Type consistency --- */

/* TODO: Implement termConsistent.
   Structural consistency: like equality but holes match anything.
   Hole(_) is consistent with anything.
   Identifier(x) is consistent with Identifier(y) when x == y.
   StringLit(x) is consistent with StringLit(y) when x == y.
   Ap(f1, args1) is consistent with Ap(f2, args2) when f1~f2 and args pairwise consistent (same length).
   List, Cons, Comma, Arrow, Asc: recurse structurally.
   Everything else: false. */
let rec termConsistent = (_a: term, _b: term): bool =>
  failwith("TODO")

/* TODO: Implement consistent.
   Optional wrapper: None is consistent with anything.
   Some(a) is consistent with Some(b) when termConsistent(a, b). */
and consistent = (_t1: option(term), _t2: option(term)): bool =>
  failwith("TODO");

/* --- Context lookup (OL mode) --- */

type lookupResult =
  | Found(option(fullType))
  | NotFound;

let sortTerm = mk(Identifier("Sort"));

/* TODO: Implement lookupCtx.
   If x == "Sort", return Found(Some(([], sortTerm))).
   Otherwise look up x in ctx:
     - Some(OL(ft)) => Found(ft)
     - Any other binding or None => NotFound */
let lookupCtx = (_ctx: context, _x: string): lookupResult =>
  failwith("TODO");

/* --- Error helpers --- */

/* TODO: Implement subsume.
   Check that inferred type is consistent with expected type.
   If inferred has params remaining and expected is not None, emit "Too few arguments".
   If inferred output is inconsistent with expected, emit "Inconsistency (expected ..., got ...)".
   Return the list of errors. */
let subsume =
    (_expected: option(term), _inferred: option(fullType), _from, _to_)
    : list(error) =>
  failwith("TODO");

/* TODO: Implement checkArity.
   If expected == found, return [].
   If expected > found, return ["Too few arguments"].
   If expected < found, return ["Too many arguments"]. */
let checkArity = (_expected, _found, _from, _to_) =>
  failwith("TODO");

/* TODO: Implement ensureMode.
   If stringOfMode(mode) is in the allowed list, return [].
   Otherwise return a sort error listing the allowed modes and the actual mode. */
let ensureMode = (_allowed, _mode, _from, _to_) =>
  failwith("TODO");

/* --- Extracting params (name + type) from a function signature --- */

/* TODO: Implement extractParams.
   Map over args. For each arg:
     - Asc(name, ty): extract identifier name as Some(string), pair with ty
     - anything else: (None, arg) */
let extractParams = (_args: list(term)): list((option(string), term)) =>
  failwith("TODO");

/* === ML type utilities === */

let addParens = (t: term): term =>
  switch (t.value) {
  | Identifier(_) => t
  | _ => {...t, meta: {...t.meta, parens: true}}
  };

/* ML type conversion stubs — not part of this assignment */
let rec mlTypeToTerm =
  fun
  | MTerm => mk(Identifier("Term"))
  | MSort => mk(Identifier("Sort"))
  | MBool => mk(Identifier("Bool"))
  | MString => mk(Identifier("String"))
  | MList(_) => mk(Identifier("TODO"))
  | MResult(_) => mk(Identifier("TODO"))
  | MPair(_, _) => mk(Identifier("TODO"))
  | MArrow(_, _) => mk(Identifier("TODO"));

let mlInferred = (_ty: mlType): option(fullType) =>
  Some(([], hole));

let mlSubsume = (_expected: mlType, _got: mlType, _from, _to_): list(error) =>
  [];

let rec termToMlType = (_t: term): option(mlType) =>
  Some(MTerm);

let getInferredMlType = (_info: staticInfo): mlType =>
  MTerm;

/* --- OL scope checking: strict when OL bindings exist, permissive otherwise --- */

let hasOLBindings = (ctx: context): bool =>
  StringMap.exists((_, v) => switch (v) { | OL(_) => true | ML(_) | Builtin(_) | SchemaBinding(_) | MetaLet(_, _) => false }, ctx);

/* Signature = (Term, List (Term, Term), Term) — name (as OL identifier), params (name as Identifier term, type), return type */
let signatureType = MPair(MTerm, MPair(MList(MPair(MTerm, MTerm)), MTerm));

/* Schema type: List Signature -> Result (List Term) */
let schemaType = MArrow(MList(signatureType), MResult(MList(MTerm)));

/* ML builtins context — not part of this assignment */
let mlBuiltins: context = StringMap.empty;


/* === Unified checker: OL and ML mutually recursive === */

/* TODO: Implement checkDecls.
   Fold over body, checking each line in Line mode.
   Thread the context: each line's bindings extend the context for subsequent lines.
   Return (merged staticInfo, final context). */
let rec checkDecls = (_ctx: context, _body: list(term)): (staticInfo, context) =>
  failwith("TODO")

/* TODO: Implement checkTerm.
   Handle the following cases:

   Postulate(body, rest):
     - Check body via checkDecls
     - Check rest (if any) in Program mode with the extended context
     - Ensure mode is "program"

   Identifier(v) in Expression mode:
     - Look up v via lookupCtx
     - If not found, emit "Unbound variable" error
     - If found, subsume against expected type

   Asc(left, right):
     - Line mode: check left in Spine, right in Expression(Some(hole)), bind the name
     - Argument mode: check left in IdentifierMode, right in Expression(Some(hole)), bind if no errors
     - Other: mode error

   Ap(f, args):
     - Program mode: fold items sequentially, threading context
     - Spine mode: check f in IdentifierMode, args in Argument mode, threading bindings
     - Expression mode: check f, look up its type, check args against param types with
       dependent substitution, verify arity, subsume return type

   Hole(_): in Expression mode produce hole info; otherwise error
   Shard(_), BuilderError: produce error if position >= 0

   Everything else: emptyInfo */
and checkTerm = (_ctx: context, _mode: checkingMode, _t: term): staticInfo =>
  failwith("TODO")

/* === ML checker — stubs for this assignment === */

and checkSchema = (_ctx: context, _body: term): staticInfo =>
  emptyInfo

and checkPat = (ctx: context, _ty: mlType, _t: term): (context, staticInfo) =>
  (ctx, emptyInfo)

and checkOLPat = (ctx: context, _t: term): (context, staticInfo) =>
  (ctx, emptyInfo)

and inferExpr = (_ctx: context, _t: term): staticInfo =>
  emptyInfo

and checkExpr = (_ctx: context, _expected: mlType, _t: term): staticInfo =>
  emptyInfo;

let getStatics = (t: term): staticInfo =>
  checkTerm(StringMap.empty, Program, t);
