exception UnexpectedText of string * string * Lexing.position * Lexing.position

let assert_text_is (token_text, beg_pos, end_pos) text =
  if token_text <> text then
    raise (UnexpectedText (token_text, text, beg_pos, end_pos))
