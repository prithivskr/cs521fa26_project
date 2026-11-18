(* Writes the extracted chain-reduction kernels (see ChainReduceExtract.v).
   Usage: chain_emit [DIR]       -> K=4 original and receive-first kernels
          chain_emit DIR K       -> receive-first kernel for K, written to
                                    DIR/chain-reduce-recvfirst-K<K>.json *)
let write directory (name, text) =
  let out = open_out_bin (Filename.concat directory name) in
  Fun.protect ~finally:(fun () -> close_out out) (fun () -> output_string out text)

let () =
  let directory = if Array.length Sys.argv > 1 then Sys.argv.(1) else "generated-spada" in
  if not (Sys.file_exists directory) then Sys.mkdir directory 0o755;
  if Array.length Sys.argv > 2 then begin
    let k = int_of_string Sys.argv.(2) in
    if k < 2 then (prerr_endline "chain_emit: K must be >= 2"; exit 2);
    let name = Printf.sprintf "chain-reduce-recvfirst-K%d.json" k in
    write directory (name, Chain_generated.recvfirst_json k);
    print_endline (Filename.concat directory name)
  end else
    List.iter (write directory)
      ["chain-reduce.json", Chain_generated.ChainReduce.coq_K4_json;
       "chain-reduce-recvfirst.json", Chain_generated.ChainReduceRecvFirst.coq_K4_json]
