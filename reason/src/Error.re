type error = {
  type_: string,
  message: string,
  from: int,
  to_: int,
};

let mark = (message, from, to_) => {type_: "mark", message, from, to_};

/* Non-fatal diagnostic — same `error` shape, distinguished by type_.
   Used for shadowing notices and other "this is suspicious but the
   program still typechecks" issues. Excluded from completeness
   downgrades and rendered with Warning severity in the extension. */
let warn = (message, from, to_) => {type_: "warning", message, from, to_};

/* True if any element is a real error (i.e. not a warning). */
let hasRealErrors = (errs: list(error)): bool =>
  List.exists((e) => e.type_ != "warning", errs);
