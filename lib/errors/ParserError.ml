exception UnexpectedText of string * Lexing.position * Lexing.position

let assert_text_is (token_text, beg_pos, end_pos) text =
  if token_text <> text then
    raise
      (UnexpectedText
         ( Format.sprintf "Unexpected text : '%s'. Expected : '%s'" token_text
             text,
           beg_pos,
           end_pos ))
