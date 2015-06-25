(*s Websocket server for web interface *)

(*i*)
open Abbrevs
open Core.Std

module WS = Websocket_lwt
module YS = Yojson.Safe

(*
open Util

open Tactic
open CoreRules
open TheoryTypes
open TheoryState

module PU = ParserUtil
(*i*)
*)
let (>>=) = Lwt.bind

let ps_file  = ref ""
let ps_files = ref []
let disallow_save = ref false
let new_dir = ref ""
let server_name = ref "localhost"

(*i ----------------------------------------------------------------------- i*)
(* \hd{Eval} *)

let split_proof_script s =
  let rec find_dot i =
    try
      match s.[i] with
      | '.' ->
        Some i
      | '"' ->
        find_dot (find_quote (i+1))
      | '(' when s.[i+1] = '*' ->
        find_dot (find_comment_end (i+2))
      | _ ->
        find_dot (i+1)
    with
      Invalid_argument _ -> None
  and find_comment_end i =
    match s.[i] with
    | '*' when s.[i+1] = ')' -> i+2
    | _ -> find_comment_end (i+1)
  and find_quote i =
    match s.[i] with
    | '"' -> i+1
    | _   -> find_quote (i+1)
  in
  let rec go i in_proof acc1 acc2 =
    let get_cmd j =
      String.sub s ~pos:i ~len:(j - i)
    in
    match find_dot i, in_proof with
    | Some j, false ->
      let cmd = get_cmd j in
      F.printf "cmd: ``%s''\n" cmd;
      if String.suffix cmd (String.length "proof") = "proof"
      then go (j+1) true     (acc1)      []
      else go (j+1) in_proof (cmd::acc1) acc2
    | Some j, true ->
      go (j+1) true (acc1) (get_cmd j::acc2)
    | None,_ ->
      (List.rev acc1, List.rev acc2)
  in
  go 0 false [] []

(*i ----------------------------------------------------------------------- i*)
(* \hd{Handlers for different commands} *)

let frame_of_string s = WS.Frame.create ~content:s ()

let process_unknown s =
  F.printf "unknown command: %s\n%!" s;
  Lwt.return (frame_of_string "Unknown command")


let process_list_files () =
  Lwt.return
    (frame_of_string
       (YS.to_string
          (`Assoc [("cmd", `String "setFiles");
                   ("arg", `List (List.map ~f:(fun s -> `String s) !ps_files))])))


let process_get_debug () =
  Lwt.return
    (frame_of_string
       (YS.to_string
          (`Assoc [("cmd", `String "setDebug");
                   ("arg", `String "FIXME: add debugging information")])))


let process_save filename content =
  F.printf "Save %s: %s\n%!" filename content;
  Lwt.return (
    if (Sys.file_exists !ps_file = `Yes && List.mem !ps_files filename
         && not !disallow_save) then (
      Out_channel.write_all filename ~data:content;
      frame_of_string (YS.to_string (`Assoc [("cmd", `String "saveOK")]))
    ) else if (!new_dir <> "") then (
      Out_channel.write_all (!new_dir^"/"^filename) ~data:content;
      ps_files := (!new_dir^"/"^filename) :: !ps_files;
      frame_of_string (YS.to_string (`Assoc [("cmd", `String "saveOK")]))
    ) else (
        frame_of_string (YS.to_string (`Assoc [("cmd", `String "saveFAILED")]))
    )
  )

let process_load s =
  (* Hashtbl.clear ts_cache; *)
  ps_file := if s = "" then !ps_file else s;
  F.printf "Loading %s\n%!" !ps_file;
  let s =
    if Sys.file_exists !ps_file = `Yes(* && List.mem !ps_file !ps_files *)
    then In_channel.read_all !ps_file
    else "(* Enter proof script below *)"
  in
  let res = `Assoc [("cmd", `String "setProof");
                    ("arg", `String s);
                    ("filename", `String !ps_file) ] in
  Lwt.return (frame_of_string (YS.to_string res))


let process_eval _fname proofscript =
  let res = 
    try
      let add_dots l = L.map ~f:(fun s -> s^".") l |> String.concat in
      let def_cmds, proof_cmds = split_proof_script proofscript in
      let s = Analyze.analyze_unbounded_ws (add_dots def_cmds) (add_dots proof_cmds) in
      Result.Ok s
    with
    | e ->
      Result.Error
        (F.sprintf "unknown error: %s,\n%s"
           (Exn.to_string e)
           (Exn.backtrace ()))
  in
  let ok_upto = String.length proofscript in
  let goal, err = match res with
    | Result.Ok s    -> s, ""
    | Result.Error s -> "", s
  in
  let res =
    `Assoc [ ("cmd", `String "setGoal");
             ("ok_upto", `Int ok_upto);
             ("debug", `String "" (*i (Buffer.contents buf) i*));
             ("err", `String err);
             ("msgs", `List [`String "some message"]);
             ("arg", `String goal) ]
  in
  Lwt.return (frame_of_string (YS.to_string res))

(*i ----------------------------------------------------------------------- i*)
(* \hd{Frame processing and server setup} *)

let process_frame frame =
  let inp = let s = WS.Frame.( frame.content ) in
	    if s = "" then failwith "frame error"
	    else s 
  in
  F.printf "Command: ``%s''\n%!" inp;
  match YS.from_string inp with
  | `Assoc l ->
     begin
       try
         let get k = List.Assoc.find_exn l k in
         match get "cmd", get "arg" with
         | `String cmd, `String arg when cmd = "eval" || cmd = "save" ->
           begin match get "filename" with
           | `String fname ->
             begin match cmd with
             | "eval" -> process_eval fname arg
             | "save" -> process_save fname arg
             | _ -> assert false
             end
           | _ -> process_unknown inp
           end
         | `String "load", `String fname -> process_load fname
         | `String "listFiles", _        -> process_list_files ()
         | `String "getDebug", _         -> process_get_debug ()
         | _                             -> process_unknown inp
       with Not_found -> process_unknown inp
     end
  | _ -> process_unknown inp

let sockaddr_of_dns node service =
  Lwt_unix.(
    getaddrinfo node service [AI_FAMILY(PF_INET); AI_SOCKTYPE(SOCK_STREAM)] >>= fun s ->
    match s with
    | h::_ -> Lwt.return h.Lwt_unix.ai_addr
    | []   -> Lwt.fail Not_found)

let run_server node service =
  let rec _zoocrypt_serve id uri stream push =
    Lwt_stream.next stream >>= fun frame ->
    process_frame frame >>= fun frame' ->
    Lwt.wrap (fun () -> push (Some frame')) >>= fun () ->
    _zoocrypt_serve id uri stream push
  in

  let echo_fun _id _req recv send =
    let react _fr =
      send @@ WS.Frame.create ~opcode:WS.Frame.Opcode.Pong ~content:"asdf\n" ()
    in
    let rec react_forever () = recv () >>= react >>= react_forever
    in
    react_forever ()
  in
  let uri = Uri.of_string ("ws://" ^ node ^ ":" ^ service) in
  Resolver_lwt.resolve_uri ~uri Resolver_lwt_unix.system >>= fun endp ->
  Conduit_lwt_unix.(endp_to_server ~ctx:default_ctx endp >>= fun server ->
  WS.establish_server ~ctx:default_ctx ~mode:server echo_fun)
 
(*
let run_server node service =
  let rec zoocrypt_serve uri (stream, push) =
    Lwt_stream.next stream >>= fun frame ->
    process_frame frame >>= fun frame' ->
    Lwt.wrap (fun () -> push (Some frame')) >>= fun () ->
    zoocrypt_serve uri (stream, push)
  in
  sockaddr_of_dns node service >>= fun sa ->
  Lwt.return (WS.establish_server ~ctx:default_ctx sa zoocrypt_serve)
*)  

let rec wait_forever () =
  Lwt_unix.sleep 1000.0 >>= wait_forever

(*i ----------------------------------------------------------------------- i*)
(* \hd{Argument handling} *)

let main =
  Printexc.record_backtrace true;
  let speclist =
    Arg.align
      [ ("-nosave", Arg.Set disallow_save, " disallow to save file");
        ("-new_dir", Arg.Set_string new_dir,
         " allow creation of new files in given directory");
        ("-s", Arg.Set_string server_name, " bind to this servername (default: localhost)")]
  in
  let usage_msg = "Usage: " ^ Sys.argv.(0) ^ " <file>" in
  let parse_args s = ps_files := !ps_files @ [s] in
  Arg.parse speclist parse_args usage_msg;
  if !ps_files = [] then (Arg.usage speclist usage_msg; exit 1);
  ps_file := List.hd_exn !ps_files;

  (* start server *)
  print_endline "Open the following URL in your browser (websocket support required):\n";
  print_endline ("    file://"^Sys.getcwd ()^"/web/index.html\n\n");
  if Sys.file_exists !ps_file = `Yes
  then print_endline ("Files: " ^ (String.concat ~sep:", " !ps_files))
  else failwith (F.sprintf "File ``%s'' does not exist." !ps_file);
  Lwt_main.run (run_server !server_name "9999" >>= fun _ -> wait_forever ())
