let () =
  let directory = if Array.length Sys.argv > 1 then Sys.argv.(1) else "generated-spada" in
  if not (Sys.file_exists directory) then Sys.mkdir directory 0o755;
  List.iter (fun (name, contents) ->
    let channel = open_out_bin (Filename.concat directory name) in
    Fun.protect ~finally:(fun () -> close_out channel)
      (fun () -> output_string channel contents))
    [ "ping.json", Spada_generated.ping_json;
      "multicast.json", Spada_generated.multicast_json;
      "pipeline.json", Spada_generated.pipeline_json;
      "host.json", Spada_generated.host_json;
      "fixtures.json", Spada_generated.fixtures_json;
      "epochs.json", Spada_generated.epochs_json;
      "meta.json", Spada_generated.meta_json;
      "bounded.json", Spada_generated.bounded_json;
      "external.json", Spada_generated.external_json;
      "manual-ping.json", Spada_generated.manual_ping_json ]
  ; List.iter (fun (name, contents) -> match contents with
      | None -> failwith ("Rocq routing failed: " ^ name)
      | Some contents -> let channel = open_out_bin (Filename.concat directory name) in
        Fun.protect ~finally:(fun () -> close_out channel)
          (fun () -> output_string channel contents))
    ["ping-routes.inc.csl", Spada_generated.ping_routing_text;
     "multicast-routes.inc.csl", Spada_generated.multicast_routing_text]
