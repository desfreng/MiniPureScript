include X86_64

let add (text, data) (t, d) = (text ++ t, data ++ d)

let add_text (text, data) t = (text ++ t, data)

let add_data (text, data) d = (text, data ++ d)

let log_fun asm log_lbl =
  (* We add the *)
  let asm = add_data asm (label log_lbl) in
  let asm = add_text asm (movq (ind ~ofs:8 rsp) !%rsi) in
  let asm = add_text asm (movq (ind ~ofs:8 rsp) !%rsi) in
  asm
