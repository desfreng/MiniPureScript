let good_test _ () = assert false
let bad_test _ () = assert false

let () =
  let good_list, bad_list =
    Files.(
      List.fold_left
        (fun (good, bad) t ->
          match t with
          | ExecTest (file, _) | TypingTest (file, true) ->
              let filename = Filename.basename file in
              (Alcotest.test_case filename `Quick (good_test file) :: good, bad)
          | TypingTest (file, false) ->
              let filename = Filename.basename file in
              (good, Alcotest.test_case filename `Quick (bad_test file) :: bad)
          | SyntaxTest _ -> (good, bad))
        ([], []) files)
  in
  Alcotest.run "Partie 2" [ ("good", good_list); ("bad", bad_list) ]
