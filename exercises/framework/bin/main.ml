open Format
open Lexing

let usage = "usage: framework [options] file.crdt"

let parse_only = ref false
let type_only  = ref false
let debug      = ref false

let spec =
  [
    "--debug",      Arg.Set debug,      "  debug mode";
    "--parse-only", Arg.Set parse_only, "  stop after parsing";
    "--type-only",  Arg.Set type_only,  "  stop after typing";
  ]

let file =
  let file = ref None in
  let set_file s =
    if not (Filename.check_suffix s ".crdt") then
      raise (Arg.Bad "no .crdt extension");
    file := Some s
  in
  Arg.parse spec set_file usage;
  match !file with Some f -> f | None -> Arg.usage spec usage; exit 1

let report (b, e) =
  let l  = b.pos_lnum in
  let fc = b.pos_cnum - b.pos_bol + 1 in
  let lc = e.pos_cnum - b.pos_bol + 1 in
  eprintf "File \"%s\", line %d, characters %d-%d:\n" file l fc lc

let () =
  let c  = open_in file in
  let lb = Lexing.from_channel c in
  try
    let f = Framework.Parser.file Framework.Lexer.next_token lb in
    close_in c;
    if !parse_only then exit 0;
    let f = Framework.Typing.file ~debug:!debug f in
    if !type_only then exit 0;
    let out_file = Filename.chop_suffix file ".crdt" ^ ".mlw" in
    let oc = open_out out_file in
    let fmt = Format.formatter_of_out_channel oc in
    Framework.Printer.write_w3_tfile fmt f;
    Format.pp_print_flush fmt ();
    close_out oc
  with
  | Framework.Lexer.Lexing_error s ->
      report (lexeme_start_p lb, lexeme_end_p lb);
      eprintf "lexical error: %s@." s;
      exit 1
  | Framework.Parser.Error ->
      report (lexeme_start_p lb, lexeme_end_p lb);
      eprintf "syntax error@.";
      exit 1
  | Framework.Typing.Error (loc, s) ->
      report loc;
      eprintf "error: %s@." s;
      exit 1
  | e ->
      eprintf "anomaly: %s\n@." (Printexc.to_string e);
      exit 2