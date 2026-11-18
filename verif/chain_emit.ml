(* Writes the extracted chain-reduction kernels (see ChainReduceExtract.v). *)
let () =
  let directory = if Array.length Sys.argv > 1 then Sys.argv.(1) else "generated-spada" in
  if not (Sys.file_exists directory) then Sys.mkdir directory 0o755;
  List.iter (fun (name, text) ->
    let out = open_out_bin (Filename.concat directory name) in
    Fun.protect ~finally:(fun () -> close_out out) (fun () -> output_string out text))
    ["chain-reduce.json", Chain_generated.ChainReduce.coq_K4_json;
     "chain-reduce-recvfirst.json", Chain_generated.ChainReduceRecvFirst.coq_K4_json]
