let (>>=) = Lwt.bind
 
let get_contents stream =
  let rec f = function
    | None -> Lwt.return_unit
    | Some fr -> Lwt_stream.get stream >>= f in
  Lwt_stream.get stream >>= f
 
let cxn_fn uri (stream, _) =
  get_contents stream >>= fun () -> Lwt_io.printl "user disconnected"
 
let sockaddr_of_dns node service =
  let open Lwt_unix in
  Lwt.map (fun ai -> ai.ai_addr)
    (getaddrinfo node service [AI_FAMILY(PF_INET); AI_SOCKTYPE(SOCK_STREAM)] >>=
   function h::t -> Lwt.return h
                      | [] -> Lwt.fail Not_found)
 
let rec wait_forever () = Lwt_unix.sleep 1000. >>= wait_forever
 
let run_server node service =
  sockaddr_of_dns node service >>= fun sa ->
  Lwt.return (Websocket.establish_server sa cxn_fn) >>= fun _ -> wait_forever ()
 
let () = Lwt_main.run (run_server "0.0.0.0"  "7890")
