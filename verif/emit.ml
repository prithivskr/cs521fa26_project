(* Only file I/O lives outside Rocq. All CSL contents come from extraction. *)
let () =
  let directory = if Array.length Sys.argv > 1 then Sys.argv.(1) else "generated" in
  if not (Sys.file_exists directory) then Sys.mkdir directory 0o755;
  match Generated.example_files with
  | None -> failwith "Rocq compiler rejected the example"
  | Some files ->
      List.iter (fun (name, contents) ->
        let channel = open_out_bin (Filename.concat directory name) in
        Fun.protect ~finally:(fun () -> close_out channel)
          (fun () -> output_string channel contents)) files
