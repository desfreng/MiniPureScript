open MiniPureScriptLib

let lexer_of_str txt =
  let lexbuf = Lexing.from_string txt in
  fun () -> Lexer.gen_pretokens lexbuf

let a_token = Alcotest.testable Utils.pp_token ( = )

let test_string () =
  let p = lexer_of_str "eee" in
  Alcotest.(check a_token) "This is a test" (p ()).t (LINDENT "eee")

let () =
  Alcotest.run "Utils"
    [ ("string-case", [ Alcotest.test_case "Lower case" `Quick test_string ]) ]
