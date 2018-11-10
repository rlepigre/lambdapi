(** Parsing functions for the Lambdapi syntax. *)

open Earley_core
open Extra
open Console
open Syntax
open Files
open Pos

#define LOCATE locate

(** Prefix trees for greedy parsing among a set of string. *)
module Prefix :
  sig
    (** Type of a prefix tree. *)
    type 'a t

    (** [init ()] initializes a new (empty) prefix tree. *)
    val init : unit -> 'a t

    (** [reset t] resets [t] to an empty prefix tree [t]. *)
    val reset : 'a t -> unit

    (** [add k v t] inserts the value [v] with the key [k] (possibly replacing
        a previous value associated to [k]) in the tree [t]. *)
    val add : 'a t -> string -> 'a -> unit

    (** [grammar t] is an [Earley] grammar parsing the longest possible prefix
        of the input corresponding to a word of [t]. The corresponding, stored
        value is returned. It fails if no such longest prefix exist. *)
    val grammar : 'a t -> 'a Earley.grammar
  end =
  struct
    type 'a tree = Node of 'a option * (char * 'a tree) list
    type 'a t = 'a tree Pervasives.ref

    let init : unit -> 'a t = fun _ -> ref (Node(None, []))

    let reset : 'a t -> unit = fun t -> t := Node(None, [])

    let add : 'a t -> string -> 'a -> unit = fun t k v ->
      let rec add i (Node(vo,l)) =
        match try Some(k.[i]) with _ -> None with
        | None    -> Node(Some(v), l)
        | Some(c) ->
            let l =
              try
                let t = List.assoc c l in
                (c, add (i+1) t) :: (List.remove_assoc c l)
              with Not_found -> (c, add (i+1) (Node(None, []))) :: l
            in
            Node(vo, l)
      in
      t := add 0 !t

    let grammar : 'a t -> 'a Earley.grammar = fun t ->
      let fn buf pos =
        let rec fn best (Node(vo,l)) buf pos =
          let best =
            match vo with
            | None    -> best
            | Some(v) -> Some(v,buf,pos)
          in
          try
            let (c, buf, pos) = Input.read buf pos in
            fn best (List.assoc c l) buf pos
          with Not_found ->
            match best with
            | None       -> Earley.give_up ()
            | Some(best) -> best
        in fn None !t buf pos
      in
      (* FIXME charset, accept empty ? *)
      Earley.black_box fn Charset.full false "<tree>"
  end

(** Currently defined binary operators. *)
let binops : binop Prefix.t = Prefix.init ()

(** Parser for a binary operator. *)
let binop = Prefix.grammar binops

(** [get_binops mp] loads the binary operators associated to module path [mp].
    Note that this requires the module to be loaded (i.e., compile). *)
let get_binops : module_path -> unit = fun mp ->
  let sign =
    try PathMap.find mp Timed.(!(Sign.loaded)) with Not_found ->
      fatal_no_pos "Module [%a] not loaded (used for binops)." pp_path mp
  in
  let fn s (_, binop) = Prefix.add binops s binop in
  StrMap.iter fn Timed.(!Sign.(sign.sign_binops))

(** Blank function (for comments and white spaces). *)
let blank = Blanks.line_comments "//"

(** Keyword module. *)
module KW = Keywords.Make(
  struct
    let id_charset = Charset.from_string "a-zA-Z0-9_"
    let reserved = []
  end)

(** Reserve ["KIND"] to disallow it as an identifier. *)
let _ = KW.reserve "KIND"

(** Keyword declarations. *)
let _require_    = KW.create "require"
let _open_       = KW.create "open"
let _as_         = KW.create "as"
let _let_        = KW.create "let"
let _in_         = KW.create "in"
let _symbol_     = KW.create "symbol"
let _definition_ = KW.create "definition"
let _theorem_    = KW.create "theorem"
let _rule_       = KW.create "rule"
let _and_        = KW.create "and"
let _assert_     = KW.create "assert"
let _assertnot_  = KW.create "assertnot"
let _const_      = KW.create "const"
let _inj_        = KW.create "injective"
let _TYPE_       = KW.create "TYPE"
let _pos_        = KW.create "pos"
let _neg_        = KW.create "neg"
let _proof_      = KW.create "proof"
let _refine_     = KW.create "refine"
let _intro_      = KW.create "intro"
let _apply_      = KW.create "apply"
let _simpl_      = KW.create "simpl"
let _rewrite_    = KW.create "rewrite"
let _refl_       = KW.create "reflexivity"
let _sym_        = KW.create "symmetry"
let _focus_      = KW.create "focus"
let _print_      = KW.create "print"
let _qed_        = KW.create "qed"
let _admit_      = KW.create "admit"
let _abort_      = KW.create "abort"
let _set_        = KW.create "set"
let _wild_       = KW.create "_"
let _proofterm_  = KW.create "proofterm"

(** Natural number literal. *)
let nat_lit =
  let num_cs = Charset.from_string "0-9" in
  let fn buf pos =
    let nb = ref 1 in
    while Charset.mem num_cs (Input.get buf (pos + !nb)) do incr nb done;
    (int_of_string (String.sub (Input.line buf) pos !nb), buf, pos + !nb)
  in
  Earley.black_box fn num_cs false "<nat>"

(** Floating-point number literal. *)
let float_lit =
  let num_cs = Charset.from_string "0-9" in
  let fn buf pos =
    let nb = ref 1 in
    while Charset.mem num_cs (Input.get buf (pos + !nb)) do incr nb done;
    if Input.get buf (pos + !nb) = '.' then
      begin
        incr nb;
        while Charset.mem num_cs (Input.get buf (pos + !nb)) do incr nb done;
      end;
    (float_of_string (String.sub (Input.line buf) pos !nb), buf, pos + !nb)
  in
  Earley.black_box fn num_cs false "<float>"

(** String literal. *)
let string_lit =
  let body_cs = List.fold_left Charset.del Charset.full ['"'; '\n'] in
  let fn buf pos =
    let nb = ref 1 in
    while Charset.mem body_cs (Input.get buf (pos + !nb)) do incr nb done;
    if Input.get buf (pos + !nb) <> '"' then Earley.give_up ();
    (String.sub (Input.line buf) (pos+1) (!nb-1), buf, pos + !nb + 1)
  in
  Earley.black_box fn (Charset.singleton '"') false "<string>"

(** Sequence of alphabetical characters. *)
let alpha =
  let alpha = Charset.from_string "a-zA-Z" in
  let fn buf pos =
    let nb = ref 1 in
    while Charset.mem alpha (Input.get buf (pos + !nb)) do incr nb done;
    (String.sub (Input.line buf) pos !nb, buf, pos + !nb)
  in
  Earley.black_box fn alpha false "<alpha>"

(** Regular identifier (regexp ["[a-zA-Z_][a-zA-Z0-9_]*"]). *)
let regular_ident =
  let head_cs = Charset.from_string "a-zA-Z_" in
  let body_cs = Charset.from_string "a-zA-Z0-9_" in
  let fn buf pos =
    let nb = ref 1 in
    while Charset.mem body_cs (Input.get buf (pos + !nb)) do incr nb done;
    (String.sub (Input.line buf) pos !nb, buf, pos + !nb)
  in
  Earley.black_box fn head_cs false "<r-ident>"

(** Escaped identifier (regexp ["{|\([^|]\|\(|[^}]\)\)|*|}"]). *)
let escaped_ident =
  let fn buf pos =
    let s = Buffer.create 20 in
    (* Check start marker. *)
    let (c, buf, pos) = Input.read buf (pos + 1) in
    if c <> '|' then Earley.give_up ();
    Buffer.add_string s "{|";
    (* Accumulate until end marker. *)
    let rec work buf pos =
      let (c, buf, pos) = Input.read buf pos in
      let next_c = Input.get buf pos in
      if c = '|' && next_c = '}' then (Buffer.add_string s "|}"; (buf, pos+1))
      else if c <> '\255' then (Buffer.add_char s c; work buf pos)
      else Earley.give_up ()
    in
    let (buf, pos) = work buf pos in
    (* Return the contents. *)
    (Buffer.contents s, buf, pos)
  in
  Earley.black_box fn (Charset.singleton '{') false "<e-ident>"

(** Any identifier (regular or escaped). *)
let parser any_ident =
  | id:regular_ident -> KW.check id; id
  | id:escaped_ident -> id

(** Identifier (regular and non-keyword, or escaped). *)
let parser ident = id:any_ident -> in_pos _loc id

(** Metavariable identifier (regular or escaped, prefixed with ['?']). *)
let parser meta =
  | "?" - id:{regular_ident | escaped_ident} -> in_pos _loc id

(** Pattern variable identifier (regular or escaped, prefixed with ['&']). *)
let parser patt =
  | "&" - id:{regular_ident | escaped_ident} -> in_pos _loc id

(** Module path (dot-separated identifiers. *)
let parser path = m:any_ident ms:{"." any_ident}* $ -> m::ms

(** [qident] parses a single (possibly qualified) identifier. *)
let parser qident = mp:{any_ident "."}* id:any_ident -> in_pos _loc (mp,id)

(** [symtag] parses a single symbol tag. *)
let parser symtag =
  | _const_ -> Sym_const
  | _inj_   -> Sym_inj

(** Priority level for an expression (term or type). *)
type prio = PAtom | PBinO | PAppl | PFunc

(** [term] is a parser for a term. *)
let parser term @(p : prio) =
  (* TYPE constant. *)
  | _TYPE_
      when p >= PAtom -> in_pos _loc P_Type
  (* Variable (or possibly qualified symbol). *)
  | qid:qident
      when p >= PAtom -> in_pos _loc (P_Vari(qid))
  (* Wildcard. *)
  | _wild_
      when p >= PAtom -> in_pos _loc P_Wild
  (* Metavariable. *)
  | m:meta e:env?[[]]
      when p >= PAtom -> in_pos _loc (P_Meta(m, Array.of_list e))
  (* Pattern (LHS) or pattern application (RHS). *)
  | p:patt e:env?[[]]
      when p >= PAtom -> in_pos _loc (P_Patt(p, Array.of_list e))
  (* Parentheses. *)
  | "(" t:(term PFunc) ")"
      when p >= PAtom -> t
  (* Application. *)
  | t:(term PAppl) u:(term PBinO)
      when p >= PAppl -> in_pos _loc (P_Appl(t,u))
  (* Implication. *)
  | a:(term PAppl) "⇒" b:(term PFunc)
      when p >= PFunc -> in_pos _loc (P_Impl(a,b))
  (* Products. *)
  | "∀" xs:arg* "," b:(term PFunc)
      when p >= PFunc -> in_pos _loc (P_Prod(xs,b))
  (* Abstraction. *)
  | "λ" xs:arg* "," t:(term PFunc)
      when p >= PFunc -> in_pos _loc (P_Abst(xs,t))
  (* Local let. *)
  | _let_ x:ident a:arg* "=" t:(term PFunc) _in_ u:(term PFunc)
      when p >= PFunc -> in_pos _loc (P_LLet(x,a,t,u))
  (* Natural number literal. *)
  | n:nat_lit
      when p >= PAtom -> in_pos _loc (P_NLit(n))
  (* Binary operator. *)
  | t:(term PBinO) b:binop
      when p >= PBinO ->>
        (* Find out minimum priorities for left and right operands. *)
        let (min_pl, min_pr) =
          let (_, assoc, p, _) = b in
          let p_plus_epsilon = p +. 1e-6 in
          match assoc with
          | Assoc_none  -> (p_plus_epsilon, p_plus_epsilon)
          | Assoc_left  -> (p             , p_plus_epsilon)
          | Assoc_right -> (p_plus_epsilon, p             )
        in
        (* Check that priority of left operand is above [min_pl]. *)
        let _ =
          match t.elt with
          | P_BinO(_,(_,_,p,_),_) -> if p < min_pl then Earley.give_up ()
          | _                     -> ()
        in
        u:(term PBinO) ->
          (* Check that priority of the right operand is above [min_pr]. *)
          let _ =
            match u.elt with
            | P_BinO(_,(_,_,p,_),_) -> if p < min_pr then Earley.give_up ()
            | _                     -> ()
          in
          in_pos _loc (P_BinO(t,b,u))

(* NOTE on binary operators. To handle infix binary operators, we need to rely
   on a dependent (Earley) grammar. The operands are parsed using the priority
   level [PBinO]. The left operand is parsed first, together with the operator
   to obtain the corresponding priority and associativity parameters.  We then
   check whether the (binary operator) priority level [pl] of the left operand
   satifies the conditions, and reject it earley if it does not. We then parse
   the right operand in a second step, and also check whether is satisfied the
   required condition before accepting the parse tree. *)

(** [env] is a parser for a metavariable environment. *)
and parser env = "[" t:(term PAppl) ts:{"," (term PAppl)}* "]" -> t::ts

(** [arg] parses a single function argument. *)
and parser arg =
  | x:ident                            -> (x, None   )
  | "(" x:ident ":" a:(term PFunc) ")" -> (x, Some(a))

let term = term PFunc

(** [rule] is a parser for a single rewriting rule. *)
let parser rule =
  | l:term "→" r:term -> Pos.in_pos _loc (l, r) (* TODO *)

(** [rw_patt_spec] is a parser for a rewrite pattern specification. *)
let parser rw_patt_spec =
  | t:term                          -> P_rw_Term(t)
  | _in_ t:term                     -> P_rw_InTerm(t)
  | _in_ x:ident _in_ t:term        -> P_rw_InIdInTerm(x,t)
  | x:ident _in_ t:term             -> P_rw_IdInTerm(x,t)
  | u:term _in_ x:ident _in_ t:term -> P_rw_TermInIdInTerm(u,x,t)
  | u:term _as_ x:ident _in_ t:term -> P_rw_TermAsIdInTerm(u,x,t)

(** [rw_patt] is a parser for a (located) rewrite pattern. *)
let parser rw_patt = "[" r:rw_patt_spec "]" -> in_pos _loc r

(** [tactic] is a parser for a single tactic. *)
let parser tactic =
  | _refine_ t:term             -> Pos.in_pos _loc (P_tac_refine(t))
  | _intro_ xs:ident+           -> Pos.in_pos _loc (P_tac_intro(xs))
  | _apply_ t:term              -> Pos.in_pos _loc (P_tac_apply(t))
  | _simpl_                     -> Pos.in_pos _loc P_tac_simpl
  | _rewrite_ p:rw_patt? t:term -> Pos.in_pos _loc (P_tac_rewrite(p,t))
  | _refl_                      -> Pos.in_pos _loc P_tac_refl
  | _sym_                       -> Pos.in_pos _loc P_tac_sym
  | i:{_:_focus_ nat_lit}       -> Pos.in_pos _loc (P_tac_focus(i))
  | _print_                     -> Pos.in_pos _loc P_tac_print
  | _proofterm_                 -> Pos.in_pos _loc P_tac_proofterm

(** [proof_end] is a parser for a proof terminator. *)
let parser proof_end =
  | _qed_   -> P_proof_QED
  | _admit_ -> P_proof_admit
  | _abort_ -> P_proof_abort

(** [assertion] parses a single assertion. *)
let parser assertion =
  | t:term ":" a:term -> P_assert_typing(t,a)
  | t:term "≡" u:term -> P_assert_conv(t,u)

let parser assoc =
  | EMPTY -> Assoc_none
  | "l"   -> Assoc_left
  | "r"   -> Assoc_right

(** [config] pases a single configuration option. *)
let parser config =
  | "verbose" i:nat_lit ->
      P_config_verbose(i)
  | "debug" b:{'+' -> true | '-' -> false} - s:alpha ->
      P_config_debug(b, s)
  | "builtin" s:string_lit "≔" qid:qident ->
      P_config_builtin(s,qid)
  | "infix" a:assoc p:float_lit s:string_lit "≔" qid:qident ->
      let binop = (s, a, p, qid) in
      Prefix.add binops s binop;
      P_config_binop(binop)

let parser proof = _proof_ ts:tactic* e:proof_end -> (ts,e)

let parser assert_must_fail =
  | _assert_    -> false
  | _assertnot_ -> true

(** [!require mp] can be called to require the compilation of the module (that
    corresponds to) [mp]. The reference is set in the [Compile] module. *)
let require : (Files.module_path -> unit) Pervasives.ref = ref (fun _ -> ())

(** [cmd] is a parser for a single command. *)
let parser cmd =
  | _require_ m:{_open_ -> P_require_open}?[P_require_default] p:path
      -> !require p; if m = P_require_open then get_binops p; P_require(p,m)
  | _require_ p:path m:{_as_ n:ident -> P_require_as(n)}
      -> !require p; P_require(p,m)
  | _open_ p:path
      -> get_binops p; P_open(p)
  | _symbol_ l:symtag* s:ident ":" a:term
      -> P_symbol(l,s,a)
  | _rule_ r:rule rs:{_:_and_ rule}*
      -> P_rules(r::rs)
  | _definition_ s:ident al:arg* ao:{":" term}? "≔" t:term
      -> P_definition(false,s,al,ao,t)
  | _theorem_ s:ident ":" a:term (ts,e):proof
      -> P_theorem(s,a,ts,e)
  | mf:assert_must_fail a:assertion
      -> P_assert(mf,a)
  | _set_ c:config
      -> P_set(c)

(** [cmds] is a parser for multiple (located) commands. *)
let parser cmds = {c:cmd -> in_pos _loc c}*

(** [parse_file fname] attempts to parse the file [fname], to obtain a list of
    toplevel commands. In case of failure, a graceful error message containing
    the error position is given through the [Fatal] exception. *)
let parse_file : string -> ast = fun fname ->
  Prefix.reset binops;
  try Earley.parse_file cmds blank fname
  with Earley.Parse_error(buf,pos) ->
    let loc = Some(Pos.locate buf pos buf pos) in
    fatal loc "Parse error."

(** [parse_string fname str] attempts to parse the string [str] file to obtain
    a list of toplevel commands.  In case of failure, a graceful error message
    containing the error position is given through the [Fatal] exception.  The
    [fname] argument should contain a relevant file name for the error message
    to be constructed. *)
let parse_string : string -> string -> ast = fun fname str ->
  Prefix.reset binops;
  try Earley.parse_string ~filename:fname cmds blank str
  with Earley.Parse_error(buf,pos) ->
    let loc = Some(Pos.locate buf pos buf pos) in
    fatal loc "Parse error."
