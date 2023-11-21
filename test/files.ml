type test =
  | ExecTest of string * string (* filename, expected output *)
  | SyntaxTest of string * bool (* filename, bad <=> false *)
  | TypingTest of string * bool (* filename, bad <=> false *)

let explore_dir dir f =
  Array.fold_left
    (fun acc name ->
      if Filename.extension name = ".purs" then
        let file = Filename.concat dir name in
        f file :: acc
      else acc)
    [] (Sys.readdir dir)

let test_dir = "../../../test-files"

let exec_files =
  explore_dir (Filename.concat test_dir "exec") (fun file ->
      ExecTest (file, Filename.remove_extension file ^ ".out"))

let syntax_files =
  let syntax_dir = Filename.concat test_dir "syntax" in
  List.append
    (explore_dir (Filename.concat syntax_dir "good") (fun file ->
         SyntaxTest (file, true)))
    (explore_dir (Filename.concat syntax_dir "bad") (fun file ->
         SyntaxTest (file, false)))

let typing_files =
  let typing_dir = Filename.concat test_dir "typing" in
  List.append
    (explore_dir (Filename.concat typing_dir "good") (fun file ->
         TypingTest (file, true)))
    (explore_dir (Filename.concat typing_dir "bad") (fun file ->
         TypingTest (file, false)))

let files = exec_files @ syntax_files @ typing_files
