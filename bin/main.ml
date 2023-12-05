let usage_msg = "Usage: ppurse [ --parse-only | --type-only | --help ] <file>\n"
let type_only = ref false
let parse_only = ref false
let file_invalid_code = 1
let error = 2

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
      exit error
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
        let typ_prog = Typing.check_program prog in
        if !type_only then exit 0 else ignore typ_prog)
    with
    | Lexer.LexingError (t, p) ->
        Format.eprintf "%a@." ErrorPP.pp_lexing_error (t, p);
        exit file_invalid_code
    | Parser.Error ->
        Format.eprintf "%a@.Syntax Error.@." ErrorPP.pp_error_head
          (Lexing.lexeme_start_p lexbuf, Some (Lexing.lexeme_end_p lexbuf));
        exit file_invalid_code
    | ParserError.UnexpectedText (tt, et, bp, ep) ->
        Format.eprintf "%a@." ErrorPP.pp_parsing_error (tt, et, bp, ep);
        exit file_invalid_code
    | TypingError.TypeError (terr, bp, ep) ->
        Format.eprintf "%a@." ErrorPP.pp_typing_error (terr, bp, ep);
        exit file_invalid_code
  with
  | Sys_error s ->
      Format.eprintf "%s@." s;
      exit error
  | e ->
      Format.eprintf "Unexepected error:.@%s@." (Printexc.to_string_default e);
      exit error
