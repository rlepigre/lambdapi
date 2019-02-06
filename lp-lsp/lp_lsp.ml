(************************************************************************)
(* The λΠ-modulo Interactive Proof Assistant                            *)
(************************************************************************)

(************************************************************************)
(* λΠ-modulo serialization Toplevel                                     *)
(* Copyright 2018 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Core

module F = Format
module J = Yojson.Basic
module U = Yojson.Basic.Util

(* OCaml 4.04 compat *)
module Hashtbl = struct
  include Hashtbl
  let find_opt n d = try Some Hashtbl.(find n d) with | Not_found -> None
end

module List = struct
  include List
  let assoc_opt n d = try Some List.(assoc n d) with | Not_found -> None
end

let    int_field name dict = U.to_int    List.(assoc name dict)
let   dict_field name dict = U.to_assoc  List.(assoc name dict)
let   list_field name dict = U.to_list   List.(assoc name dict)
let string_field name dict = U.to_string List.(assoc name dict)

(* Conditionals *)
let option_empty x = match x with | None -> true | Some _ -> false
let option_cata f x d = match x with | None -> d | Some x -> f x
let option_default x d = match x with | None -> d | Some x -> x

let oint_field  name dict = option_cata U.to_int List.(assoc_opt name dict) 0
let odict_field name dict = option_default U.(to_option to_assoc (option_default List.(assoc_opt name dict) `Null)) []

module LIO = Lsp_io
module LSP = Lsp_base

(* Request Handling: The client expects a reply *)
let do_initialize ofmt ~id _params =
  let msg = LSP.mk_reply ~id ~result:(
      `Assoc ["capabilities",
       `Assoc [
          "textDocumentSync", `Int 1
        ; "documentSymbolProvider", `Bool true
        ; "hoverProvider", `Bool true
        ; "codeActionProvider", `Bool false
        ]]) in
  LIO.send_json ofmt msg

let do_shutdown ofmt ~id =
  let msg = LSP.mk_reply ~id ~result:`Null in
  LIO.send_json ofmt msg

let doc_table : (string, _) Hashtbl.t = Hashtbl.create 39
let completed_table : (string, Pure.state) Hashtbl.t = Hashtbl.create 39

(* Notification handling; reply is optional / asynchronous *)
let do_check_text ofmt ~doc =
  let final_st, diags = Lp_doc.check_text ~doc in
  Hashtbl.replace completed_table doc.uri final_st;
  LIO.send_json ofmt @@ diags

let do_change ofmt ~doc change =
  let open Lp_doc in
  LIO.log_error "checking file" (doc.uri ^ " / version: " ^ (string_of_int doc.version));
  let doc = { doc with text = string_field "text" change; } in
  do_check_text ofmt ~doc

let do_open ofmt params =
  let document = dict_field "textDocument" params in
  let uri, version, text =
    string_field "uri" document,
    int_field "version" document,
    string_field "text" document in
  let doc = Lp_doc.new_doc ~uri ~text ~version in
  begin match Hashtbl.find_opt doc_table uri with
    | None -> ()
    | Some _ -> LIO.log_error "do_open" ("file " ^ uri ^ " not properly closed by client")
  end;
  Hashtbl.add doc_table uri doc;
  do_check_text ofmt ~doc

let do_change ofmt params =
  let document = dict_field "textDocument" params in
  let uri, version  =
    string_field "uri" document,
    int_field "version" document in
  let changes = List.map U.to_assoc @@ list_field "contentChanges" params in
  let doc = Hashtbl.find doc_table uri in
  let doc = { doc with Lp_doc.version; } in
  List.iter (do_change ofmt ~doc) changes

let do_close _ofmt params =
  let document = dict_field "textDocument" params in
  let doc_file = string_field "uri" document in
  Hashtbl.remove doc_table doc_file

let grab_doc params =
  let document = dict_field "textDocument" params in
  let doc_file = string_field "uri" document in
  let start_doc, end_doc = Hashtbl.(find doc_table doc_file, find completed_table doc_file) in
  doc_file, start_doc, end_doc

let mk_syminfo file (name, _path, kind, pos) : J.t =
  `Assoc [
    "name", `String name;
    "kind", `Int kind;            (* function *)
    "location", `Assoc [
                    "uri", `String file
                  ; "range", LSP.mk_range pos
                  ]
  ]

let kind_of_type tm =
  let open Terms in
  let open Timed in
  let is_undef = option_empty !(tm.sym_def) && List.length !(tm.sym_rules) = 0 in
  match !(tm.sym_type) with
  | Vari _ ->
    13                         (* Variable *)
  | Type | Kind | Symb _ | _ when is_undef ->
    14                         (* Constant *)
  | _ ->
    12                         (* Function *)

let do_symbols ofmt ~id params =
  let file, _, final_st = grab_doc params in
  let sym = Pure.get_symbols final_st in
  let sym = Extra.StrMap.fold (fun _ (s,p) l ->
      let open Terms in
      (* LIO.log_error "sym" (s.sym_name ^ " | " ^ Format.asprintf "%a" pp_term !(s.sym_type)); *)
      option_cata (fun p -> mk_syminfo file
                      (s.sym_name, s.sym_path, kind_of_type s, p) :: l) p l) sym [] in
  let msg = LSP.mk_reply ~id ~result:(`List sym) in
  LIO.send_json ofmt msg

let get_docTextPosition params =
  let document = dict_field "textDocument" params in
  let file = string_field "uri" document in
  let pos = dict_field "position" params in
  let line, character = int_field "line" pos, int_field "character" pos in
  file, line, character

let do_hover ofmt ~id params =
  let _ = get_docTextPosition params in
  let result = `Assoc [ "contents", `String "hover XXX"] in
  let msg = LSP.mk_reply ~id ~result in
  LIO.send_json ofmt msg

(* XXX: We could split requests and notifications but with the OCaml
   theading model there is not a lot of difference yet; something to
   think for the future. *)
let dispatch_message ofmt dict =
  let id     = oint_field "id" dict in
  let params = odict_field "params" dict in
  match string_field "method" dict with
  (* Requests *)
  | "initialize" ->
    do_initialize ofmt ~id params
  | "shutdown" ->
    do_shutdown ofmt ~id

  (* Symbols in the document *)
  | "textDocument/documentSymbol" ->
    do_symbols ofmt ~id params

  | "textDocument/hover" ->
    do_hover ofmt ~id params

  (* Notifications *)
  | "textDocument/didOpen" ->
    do_open ofmt params
  | "textDocument/didChange" ->
    do_change ofmt params
  | "textDocument/didClose" ->
    do_close ofmt params
  | "exit" ->
    exit 0

  (* NOOPs *)
  | "initialized"
  | "workspace/didChangeWatchedFiles" ->
    ()
  | msg ->
    LIO.log_error "no_handler" msg

let process_input ofmt (com : J.t) =
  try dispatch_message ofmt (U.to_assoc com)
  with
  | U.Type_error (msg, obj) ->
    LIO.log_object msg obj
  | exn ->
    let bt = Printexc.get_backtrace () in
    LIO.log_error "[BT]" bt;
    LIO.log_error "process_input" (Printexc.to_string exn)

let lsp_main log_file std =

  Printexc.record_backtrace true;
  LSP.std_protocol := std;

  let oc = F.std_formatter in

  let debug_oc = open_out log_file in
  LIO.debug_fmt := F.formatter_of_out_channel debug_oc;

  (* XXX: Capture better / per sentence. *)
  let lp_oc = open_out "log-lp.txt" in
  let lp_fmt = F.formatter_of_out_channel lp_oc in
  Console.out_fmt := lp_fmt;
  Console.err_fmt := lp_fmt;
  (* Console.verbose := 4; *)

  let rec loop () =
    let com = LIO.read_request stdin in
    LIO.log_object "read" com;
    process_input oc com;
    F.pp_print_flush lp_fmt (); flush lp_oc;
    loop ()
  in
  try loop ()
  with exn ->
    let bt = Printexc.get_backtrace () in
    LIO.log_error "[fatal error]" Printexc.(to_string exn);
    LIO.log_error "[BT]" bt;
    F.pp_print_flush !LIO.debug_fmt ();
    flush_all ();
    close_out debug_oc;
    close_out lp_oc

open Cmdliner

(* let bt =
 *   let doc = "Enable backtraces" in
 *   Arg.(value & flag & info ["bt"] ~doc) *)

let log_file =
  let doc = "Log to $(docv)" in
  Arg.(value & opt string "log-lsp.txt" & info ["log_file"] ~docv:"FILE" ~doc)

let std =
  let doc = "Restrict to standard LSP protocol" in
  Arg.(value & flag & info ["std"] ~doc)

let lsp_cmd =
  let doc = "LP LSP Toplevel" in
  let man = [
    `S "DESCRIPTION";
    `P "Experimental LP Toplevel with LSP support";
    `S "USAGE";
    `P "See the documentation on the project's webpage for more information"
  ]
  in
  Term.(const lsp_main $ log_file $ std),
  Term.info "lp-lsp" ~version:"0.0" ~doc ~man

let main () =
  match Term.eval lsp_cmd with
  | `Error _ -> exit 1
  | _        -> exit 0

let _ = main ()
