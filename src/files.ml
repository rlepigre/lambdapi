(** File utilities. *)

open Extra
open Console

(** [src_extension] is the expected extension for source files. *)
let src_extension : string = ".lp"

(** [obj_extension] is the expected extension for binary (object) files. *)
let obj_extension : string = ".lpo"

(** [legacy_src_extension] is the extension for legacy source files. *)
let legacy_src_extension : string = ".dk"

(** Representation of a module path (roughly, a file path). *)
type module_path = string list

(** [OrderedType] module for [module_path]. *)
module Path = struct
  type t = module_path
  let compare : t -> t -> int = Pervasives.compare
end

(* Functional maps with [module_path] keys. *)
module PathMap = Map.Make(Path)

(** [pp oc mp] prints [mp] to channel [oc]. *)
let pp_path : module_path pp = fun oc mp ->
  Format.pp_print_string oc (String.concat "." mp)

(** [module_path path] computes the [module_path] corresponding to a  relative
    file [path], which should not use [".."]. The returned list is formed with
    the subdirectories along the [path], and it is terminated by the file name
    (without extension). Although it is removed, the extension should be given
    on the file name, and it should correspond to [src_extension] (or possibly
    to the legacy extension [legacy_src_extension]).  When [path] is  invalid,
    [Invalid_argument "invalid module path"] is raised. *)
let module_path : string -> module_path = fun fname ->
  let ext_ok = Filename.check_suffix fname src_extension in
  let ext_ok = ext_ok || Filename.check_suffix fname legacy_src_extension in
  if not ext_ok then
    fatal_no_pos "Invalid file extension for [%s] (expected [%s] or [%s])."
      fname src_extension legacy_src_extension;
  if not (Filename.is_relative fname) then
    fatal_no_pos "Invalid path for [%s] (expected relative path)." fname;
  let base = Filename.chop_extension (Filename.basename fname) in
  let dir = Filename.dirname fname in
  if dir = Filename.parent_dir_name then
    fatal_no_pos "Invalid path for [%s] ([%s] not allowed)."
      fname Filename.parent_dir_name;
  let rec build_path acc dir =
    let dirbase = Filename.basename dir in
    let dirdir  = Filename.dirname  dir in
    if dirdir = Filename.parent_dir_name then
      fatal_no_pos "Invalid path for [%s] ([%s] not allowed)."
        fname Filename.parent_dir_name;
    if dirbase = Filename.current_dir_name then acc
    else build_path (dirbase::acc) dirdir
  in
  build_path [base] dir

(** [mod_time fname] returns the modification time of file [fname] represented
    as a [float]. [neg_infinity] is returned if the file does not exist. *)
let mod_time : string -> float = fun fname ->
  if Sys.file_exists fname then Unix.((stat fname).st_mtime) else neg_infinity

(** [more_recent source target] checks whether the [target] (produced from the
    [source] file) should be produced again. This is the case when [source] is
    more recent than [target]. *)
let more_recent : string -> string -> bool = fun source target ->
  mod_time source > mod_time target
