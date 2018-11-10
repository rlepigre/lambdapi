(** Interface to lp-lsp. *)

open Timed

(* Lambdapi core *)
open Core
open Core.Extra
open Core.Console

(** Representation of a single command (abstract). *)
module Command = struct
  type t = Syntax.p_cmd
  let equal x y = Syntax.eq_p_cmd x y
end

(** Exception raised by [parse_text] on error. *)
exception Parse_error of Pos.pos * string

let parse_text : string -> string -> Command.t Pos.loc list = fun fname s ->
  let old_syntax = Filename.check_suffix fname Files.legacy_src_extension in
  try
    if old_syntax then Legacy_parser.parse_string fname s
    else Parser.parse_string fname s
  with
  | Fatal(Some(Some(pos)), msg) -> raise (Parse_error(pos, msg))
  | Fatal(_              , _  ) -> assert false (* Should not produce. *)

type state = Time.t * Scope.sig_state

type result =
  | OK    of state
  | Error of Pos.popt option * string

let t0 = Time.save ()

let initial_state : Files.module_path -> state = fun path ->
  Time.restore t0;
  Sign.loading := [path];
  let sign = Sign.create path in
  Sign.loaded  := Files.PathMap.add path sign !Sign.loaded;
  (Time.save (), Scope.empty_sig_state sign)

let handle_command : state -> Command.t Pos.loc -> result = fun (st,ss) cmd ->
  Time.restore st;
  try
    let ss = Handle.handle_cmd ss cmd in
    OK(Time.save (), ss)
  with Fatal(p,m) -> Error(p,m)

let get_symbols : state -> (Terms.sym * Pos.popt) StrMap.t = fun (st,_) ->
  Time.restore st; !(Sign.((current_sign ()).sign_symbols))

(* Equality on *)
let%test _ =
  let c = parse_text "foo.lp" "symbol const B : TYPE" in
  List.equal (fun x y -> Command.equal x.Pos.elt y.Pos.elt) c c

(* Equality not *)
let%test _ =
  let c = parse_text "foo.lp" "symbol const B : TYPE" in
  let d = parse_text "foo.lp" "symbol const C : TYPE" in
  not List.(equal (fun x y -> Command.equal x.Pos.elt y.Pos.elt) c d)

(* Equality is not sensitive to whitespace *)
let%test _ =
  let c = parse_text "foo.lp" "symbol   const  B : TYPE" in
  let d = parse_text "foo.lp" "  symbol const B :   TYPE " in
  List.(equal (fun x y -> Command.equal x.Pos.elt y.Pos.elt) c d)

(* More complex test stressing most commands *)
let%test _ =
  let c = parse_text "foo.lp" "
symbol const B : TYPE

symbol const true  : B
symbol const false : B
symbol bool_neg : B ⇒ B

rule bool_neg true  → false
rule bool_neg false → true

symbol const Prop : TYPE
symbol injective P : Prop ⇒ TYPE

symbol const eq : ∀a, T a ⇒ T a ⇒ Prop

theorem notK : ∀a, P (eq bool (bool_neg (bool_neg a)) a)
proof
   intro a
qed
" in
  List.(equal (fun x y -> Command.equal x.Pos.elt y.Pos.elt) c c)

