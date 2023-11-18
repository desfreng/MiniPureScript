{
  open Lexing
  open Parser

  exception Lexing_error of string
}


rule next_tokens = parse
  | '\n'    { new_line lexbuf; next_tokens lexbuf }
  | eof     { EOF }
  | _ as c  { raise (Lexing_error ("illegal character: " ^ String.make 1 c)) }


{

}
