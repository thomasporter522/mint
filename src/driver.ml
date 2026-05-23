(* Long-lived Toploop session. `init` once, then `exec` per phrase.
   Same in-process session keeps type extensions and value bindings
   alive across calls. *)

let init () =
  Toploop.set_paths ();
  Toploop.initialize_toplevel_env ();
  Toploop.input_name := "(kernel)"

let exec (src : string) : bool =
  let lexbuf = Lexing.from_string src in
  let rec loop () =
    match
      try Some (!Toploop.parse_toplevel_phrase lexbuf)
      with End_of_file -> None
    with
    | None -> true
    | Some phrase ->
      let ok =
        try Toploop.execute_phrase true Format.std_formatter phrase
        with exn ->
          Errors.report_error Format.std_formatter exn;
          false
      in
      Format.pp_print_flush Format.std_formatter ();
      if ok then loop () else false
  in
  loop ()
