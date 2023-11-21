let exec_test _ _ () = assert false

let () =
  let exec_tests =
    Files.(
      List.fold_left
        (fun acc t ->
          match t with
          | ExecTest (file, out) ->
              let filename = Filename.basename file in
              Alcotest.test_case filename `Slow (exec_test file out) :: acc
          | _ -> acc)
        [] files)
  in
  Alcotest.run "Partie 3" [ ("Exec tests", exec_tests) ]
