(* Writes the extracted SUMMA kernels (see SummaExtract.v).
   Usage: summa_emit                      -> 2x2 example, both orders, in generated-spada/
          summa_emit DIR P MT KT NT ORDER -> DIR/summa-<order>-P<P>-<MT>x<KT>x<NT>.json
                                             (ORDER = baseline | cached) *)
let write directory (name, text) =
  let out = open_out_bin (Filename.concat directory name) in
  Fun.protect ~finally:(fun () -> close_out out) (fun () -> output_string out text)

let () =
  let argc = Array.length Sys.argv in
  if argc = 7 then begin
    let directory = Sys.argv.(1) in
    if not (Sys.file_exists directory) then Sys.mkdir directory 0o755;
    let n i = int_of_string Sys.argv.(i) in
    let p, mt, kt, nt = n 2, n 3, n 4, n 5 in
    if p < 2 || mt < 1 || kt < 1 || nt < 1 then (prerr_endline "summa_emit: need P >= 2, tiles >= 1"; exit 2);
    let cached = match Sys.argv.(6) with
      | "baseline" -> false | "cached" -> true
      | _ -> prerr_endline "summa_emit: ORDER must be baseline or cached"; exit 2 in
    let name = Printf.sprintf "summa-%s-P%d-%dx%dx%d.json" Sys.argv.(6) p mt kt nt in
    write directory (name, Summa_generated.summa_json p mt kt nt cached);
    print_endline (Filename.concat directory name)
  end else if argc = 1 then begin
    let directory = "generated-spada" in
    if not (Sys.file_exists directory) then Sys.mkdir directory 0o755;
    List.iter (write directory)
      ["summa-baseline.json", Summa_generated.Summa.baseline_json;
       "summa-cached.json", Summa_generated.Summa.optimized_json]
  end else (prerr_endline "usage: summa_emit [DIR P MT KT NT baseline|cached]"; exit 2)
