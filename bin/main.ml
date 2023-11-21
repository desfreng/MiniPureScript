open MiniPureScriptLib

let gen_tok =
  let filename = "testing/src/Main.purs" in
  let in_ch = open_in filename in
  let lexbuf = Lexing.from_channel in_ch in
  Lexing.set_filename lexbuf filename;
  fun () -> Lexer.gen_pretokens lexbuf

let rec loop () =
  let pt = gen_tok () in
  Format.printf "%a\n" Utils.pp_pretoken pt;
  if pt.t <> EOF then loop ()

let () =
  try loop ()
  with Lexer.Lexing_error (t, c) ->
    Format.eprintf "%a" Utils.pp_lexing_error (t, c);
    exit 1
