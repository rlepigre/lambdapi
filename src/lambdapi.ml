(** Main program. *)

open Core
open Extra
open Files
open Console

(* NOTE only standard [Pervasives] references here. *)

(** [confluence_checker] holds a possible confluence checking command. When it
    is given, the command should accept TPDB format on its input and the first
    line of its output yould contain either ["YES"], ["NO"] or ["MAYBE"]. *)
let confluence_checker : string option ref = ref None

(** Available modes for handling input files. *)
type execution_mode =
  | Normal    (** Type-checking (default mode).     *)
  | JustParse (** Only parse the files.             *)
  | Beautify  (** Parse and pretty-print the files. *)

(** [mode] holds the chosen exectuion mode for the run. *)
let mode = ref Normal

(** [timeout] holds a possible timeout for compilation (in seconds). *)
let timeout : int option ref = ref None

(** [handle_file fname] handles (i.e., processes) the file [fname] taking care
    of pottential errors in the process. *)
let handle_file : string -> unit = fun fname ->
  try
    (* Handle non-normal modes first. *)
    match !mode with
    | JustParse -> ignore (Compile.parse_file fname)
    | Beautify  -> Pretty.beautify (Compile.parse_file fname)
    | Normal    ->
    (* Compute the module path (checking the extension). *)
    let mp = module_path fname in
    (* Run the compilation, possibly using a timeout. *)
    let compile = Compile.compile true in
    let _ =
      match !timeout with
      | None    -> compile mp
      | Some(i) -> try with_timeout i compile mp with Timeout ->
                     fatal_no_pos "Compilation timed out for [%s]." fname
    in
    (* Possibly check the confluence. *)
    match !confluence_checker with
    | None      -> ()
    | Some(cmd) ->
    let sign = PathMap.find mp Sign.(Timed.(!loaded)) in
    match Confluence.check cmd sign with
    | Some(true ) -> ()
    | Some(false) -> fatal_no_pos "The rewrite system is not confluent."
    | None        -> fatal_no_pos "The rewrite system may not be confluent."
  with
  | Fatal(None,    msg) -> exit_with "%s" msg
  | Fatal(Some(p), msg) -> exit_with "[%a] %s" Pos.print p msg

(** [spec] contains the command line argument specification. *)
let spec =
  let set_timeout : int -> unit = fun i ->
    if i <= 0 then exit_with "Invalid timeout value [%i] (≤ 0)." i;
    timeout := Some(i)
  in
  let debug_flags =
    let fn acc l = acc ^ "\n        " ^ l in
    List.fold_left fn "\n      Available flags:" (Console.log_summary ())
  in
  let verbose_values = "\n" ^ String.concat "\n"
    [ "      Available values:"
    ; "        ≤ 0 : no output at all"
    ; "        = 1 : only file loading information (default)"
    ; "        = 2 : more file loading information"
    ; "        ≥ 3 : show the results of commands" ]
  in
  let spec = Arg.align
    [ ( "--gen-obj"
      , Arg.Set Compile.gen_obj
      , Printf.sprintf " Produce object files (%S extension)." obj_extension )
    ; ( "--toolong"
      , Arg.Float ((:=) Handle.too_long)
      , "<flt> Duration considered too long for a command." )
    ; ( "--verbose"
      , Arg.Int (Timed.(:=) verbose)
      , "<int> Set the verbosity level." ^ verbose_values )
    ; ( "--justparse"
      , Arg.Unit (fun _ -> mode := JustParse)
      , " Only parse the input files (no type-checking)." )
    ; ( "--beautify"
      , Arg.Unit (fun _ -> mode := Beautify)
      , " Parse the input files and pretty-print them (in the new syntax)." )
    ; ( "--timeout"
      , Arg.Int set_timeout
      , "<int> Use a timeout of the given number of seconds." )
    ; ( "--confluence"
      , Arg.String (fun cmd -> confluence_checker := Some(cmd))
      , "<cmd> Runs the given confluence checker." )
    ; ( "--debug"
      , Arg.String (set_debug true)
      , "<str> Sets the given debugging flags." ^ debug_flags ) ]
  in
  List.sort (fun (f1,_,_) (f2,_,_) -> String.compare f1 f2) spec

(** Main program. *)
let _ =
  (* Parse command line arguments while accumulating all files. *)
  let usage = Printf.sprintf "Usage: %s [OPTIONS] [FILES]" Sys.argv.(0) in
  let files = ref [] in
  Arg.parse spec (fun s -> files := s :: !files) usage;
  (* Compile each file separately. *)
  List.iter handle_file (List.rev !files)
