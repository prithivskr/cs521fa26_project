let () =
  let directory = "generated-spada" in
  if not (Sys.file_exists directory) then Sys.mkdir directory 0o755;
  List.iter (fun (name, text) ->
    let out = open_out_bin (Filename.concat directory name) in
    Fun.protect ~finally:(fun () -> close_out out) (fun () -> output_string out text))
    ["summa-baseline.json", Summa_generated.Summa.baseline_json;
     "summa-cached.json", Summa_generated.Summa.optimized_json]
