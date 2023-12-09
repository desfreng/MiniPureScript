let pp_error_head ppf
    ((beg_pos, end_pos) : Lexing.position * Lexing.position option) =
  let begin_col = beg_pos.pos_cnum - beg_pos.pos_bol in
  let end_col =
    match end_pos with
    | Some pos -> pos.pos_cnum - pos.pos_bol
    | None -> begin_col + 1
  in
  (* in VScode, lines start at 1, not 0 :/ *)
  (* let begin_col, end_col = (begin_col + 1, end_col + 1) in *)
  Format.fprintf ppf "File \"%s\", line %i, characters %i-%i:" beg_pos.pos_fname
    beg_pos.pos_lnum begin_col end_col

let usage_msg = "Usage: ppurse [ --parse-only | --type-only | --help ] <file>\n"
let type_only = ref false
let parse_only = ref false
let file_invalid_code = 1
let error = 2

let speclist =
  Arg.align
    [
      (* Disable '-help' because its ugly without the -- *)
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
        let typ_prog = Typing.check_program false prog in
        if !type_only then exit 0 else ignore typ_prog)
    with
    | Lexer.LexingError (terr, p) ->
        Format.eprintf "%a@.%s@." pp_error_head (p, None) terr;
        exit file_invalid_code
    | Parser.Error ->
        Format.eprintf "%a@.Syntax Error.@." pp_error_head
          (Lexing.lexeme_start_p lexbuf, Some (Lexing.lexeme_end_p lexbuf));
        exit file_invalid_code
    | ParserError.UnexpectedText (terr, bp, ep)
    | TypingError.TypeError (terr, bp, ep) ->
        Format.eprintf "%a@.%s@." pp_error_head (bp, Some ep) terr;
        exit file_invalid_code
  with Sys_error s ->
    Format.eprintf "%s@." s;
    exit error
(* | e ->
    Format.eprintf "Unexpected error:.@%s@." (Printexc.to_string_default e);
    exit error *)
