let usage_msg = "Usage: ppurse [ --parse-only | --type-only | --help ] <file>\n"
let type_only = ref false
let parse_only = ref false

let speclist =
  Arg.align
    [
      (* Disable '-help' beceause its ulgy without the -- *)
      ( "-help",
        Arg.Unit (fun () -> raise (Arg.Bad "unknown option '-help'")),
        "" );
      ("--parse-only", Arg.Set parse_only, " Only parse input file");
      ("--type-only", Arg.Set type_only, " Only type input file");
    ]

let in_file =
  let input_file = ref None in
  let set_file f =
    if Filename.check_suffix f ".purs" then input_file := Some f
    else raise (Arg.Bad "missing '.purs' extension")
  in
  Arg.parse speclist set_file usage_msg;
  match !input_file with
  | None ->
      Format.printf "%s: no input file given.@." Sys.argv.(0);
      Arg.usage speclist usage_msg;
      exit 1
  | Some f -> f

open MiniPureScriptLib

let () =
  try
    let in_chan = open_in in_file in
    let lexbuf = Lexing.from_channel ~with_positions:true in_chan in
    Lexing.set_filename lexbuf in_file;
    try
      let prog = Parser.file PostLexer.next_token lexbuf in
      close_in in_chan;
      if !parse_only then exit 0
      else (
        ignore prog;
        (* let typ_prog = Typing.check prog in *)
        (* if !type_only then exit 0 else ignore typ_prog *)
        assert false)
    with
    | Lexer.LexingError (t, p) ->
        Format.eprintf "%a@." CustomFormat.pp_lexing_error (t, p);
        exit 1
    | Parser.Error ->
        Format.eprintf "%a@.Syntax Error.@." CustomFormat.pp_error_head
          (Lexing.lexeme_start_p lexbuf, Some (Lexing.lexeme_end_p lexbuf));
        exit 1
    | ParserError.UnexpectedText (tt, et, bp, ep) ->
        Format.eprintf "%a@." CustomFormat.pp_parsing_error (tt, et, bp, ep);
        exit 1
  with
  | Sys_error s ->
      Format.eprintf "%s@." s;
      exit 2
  | e ->
      Format.eprintf "Unexepected error:.@.%s@." (Printexc.to_string_default e);
      exit 2
