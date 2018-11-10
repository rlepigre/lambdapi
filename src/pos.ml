(** Source code position management.  This module may be used to map sequences
    of characters in a source file to an abstract syntax tree. *)

open Earley_core

(** Type of a position, corresponding to a continuous range of characters in a
    (utf8-encoded) source file. Elements of this type are (lazily) constructed
    by [Earley], using the following [locate] function. *)
type pos = pos_data Lazy.t
and pos_data =
  { fname      : string option (** File name for the position.       *)
  ; start_line : int (** Line number of the starting point.          *)
  ; start_col  : int (** Column number (utf8) of the starting point. *)
  ; end_line   : int (** Line number of the ending point.            *)
  ; end_col    : int (** Column number (utf8) of the ending point.   *) }

(* NOTE laziness is essential on big files (especially those with long lines),
   because computing utf8 positions is expensive. *)

(** [locate buf1 pos1 buf2 pos2] builds a [pos] structure,  given two [Earley]
    input buffers. This function is used by Earley to generate the position of
    elements during parsing.
    @see <https://github.com/rlepigre/earley/> Earley *)
let locate : Input.buffer -> int -> Input.buffer -> int -> pos =
  fun buf1 pos1 buf2 pos2 ->
    let fn () =
      let fname = Input.filename buf1 in
      let fname = if fname = "" then None else Some(fname) in
      let start_line = Input.line_num buf1 in
      let end_line = Input.line_num buf2 in
      let start_col = Input.utf8_col_num buf1 pos1 in
      let end_col = Input.utf8_col_num buf2 pos2 in
      { fname ; start_line ; start_col ; end_line ; end_col }
    in
    Lazy.from_fun fn

(** Convenient short name for an optional position. *)
type popt = pos option

(** [equal_pos p1 p2] tells whether [p1] and [p2] denote the same location. *)
let equal_pos : pos -> pos -> bool = fun p1 p2 ->
  Lazy.force p1 = Lazy.force p2

(** [equal p1 p2] tells whether [p1] and [p2] denote the same position. *)
let equal : popt -> popt -> bool = fun p1 p2 ->
  match (p1, p2) with
  | (Some(p1), Some(p2)) -> equal_pos p1 p2
  | (None    , None    ) -> true
  | (_       , _       ) -> false

(** Type constructor extending a type (e.g. a piece of abstract syntax) with a
    a source code position. *)
type 'a loc =
  { elt : 'a   (** The element that is being localised.        *)
  ; pos : popt (** Position of the element in the source code. *) }

(** Localised string type (widely used). *)
type strloc = string loc

(** [make pos elt] associates the position [pos] to [elt]. *)
let make : popt -> 'a -> 'a loc =
  fun pos elt -> { elt ; pos }

(** [in_pos pos elt] associates the position [pos] to [elt]. *)
let in_pos : pos -> 'a -> 'a loc =
  fun p elt -> { elt ; pos = Some p }

(** [none elt] wraps [elt] in a ['a loc] structure without any specific source
    code position. *)
let none : 'a -> 'a loc =
  fun elt -> { elt ; pos = None }

(** [to_string pos] transforms [pos] into a readable string. *)
let to_string : pos -> string = fun p ->
  let {fname; start_line; start_col; end_line; end_col} = Lazy.force p in
  let fname =
    match fname with
    | None    -> ""
    | Some(n) -> n ^ ", "
  in
  if start_line <> end_line then
    Printf.sprintf "%s%d:%d-%d:%d" fname start_line start_col end_line end_col
  else if start_col = end_col then
    Printf.sprintf "%s%d:%d" fname start_line start_col
  else
    Printf.sprintf "%s%d:%d-%d" fname start_line start_col end_col

(** [print oc pos] prints the optional position [pos] to [oc]. *)
let print : Format.formatter -> pos option -> unit = fun ch p ->
  match p with
  | None    -> Format.pp_print_string ch "unknown location"
  | Some(p) -> Format.pp_print_string ch (to_string p)
