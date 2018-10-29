(** Term representation.

    This module defines the main abstract syntax tree representation for terms
    (including types), which relies on the {!module:Bindlib} library. *)

open Extra
open Timed

(** {6 Term and rewriting rules representation} *)

(** Representation of a term (or type). *)
type term =
  | Vari of term Bindlib.var
  (** Free variable. *)
  | Type
  (** "Type" constant. *)
  | Kind
  (** "Kind" constant. *)
  | Symb of sym * pp_hint
  (** Symbol (static or definable). *)
  | Prod of term * (term, term) Bindlib.binder
  (** Dependent product. *)
  | Abst of term * (term, term) Bindlib.binder
  (** Abstraction. *)
  | Appl of term * term array
  (** Application. *)
  | Meta of meta * term array
  (** Metavariable with its environment. *)
  | Patt of int option * string * term array
  (** Pattern variable (used in the LHS of rewriting rules). *)
  | TEnv of term_env * term array
  (** Term environment (used in the RHS of rewriting rules). *)
  | Wild
  (** Wildcard term (corresponding to "_" in patterns). *)
  | TRef of term option ref
  (** Reference cell (used for surface matching). *)

(* NOTE we enforce the invariant that in {!const:Appl(h,args)} the term [h] is
   not itself an application node. *)

(** Printing hint for symbols. *)
 and pp_hint =
  | Nothing             (** Just print the name of the symbol. *)
  | Qualified           (** Fully qualify the symbol name.     *)
  | Alias     of string (** Use the given alias as qualifier.  *)

(** Representation of an higher-order term. *)
 and term_env =
  | TE_Vari of term_env Bindlib.var
  (** Free higher-oder term variable (for printing only). *)
  | TE_Some of (term, term) Bindlib.mbinder
  (** Higher-order term to instantiate the RHS of rewriting rules. *)
  | TE_None
  (** Dummy higher-order term (initial value in RHS environment). *)

(** The {!const:Patt(i,s,ar)} constructor represents a pattern variable, which
    may only appear in the LHS (left hand side or pattern) of rewriting rules.
    It is identified by a {!type:string} name [s] (unique in a rewriting rule)
    and it carries an environment [ar] that should contain a set of (distinct)
    free variables (i.e., terms of the form {!const:Vari(x)}). They correspond
    to the only free variables that may appear in a matched term. Note that we
    must use the type {!type:term array} so that the variable may be bound. In
    particular, the type {!type:tvar array} would not be suitable. The element
    [i] (of type {!type:int option}) gives the index (if any) of the slot that
    is reserved for the matched term in the environment of the RHS (right hand
    side or action) of the rewriting rule. When [i] is {!const:None}, then the
    variable is not bound in the RHS. When it is {!const:Some(i)}, then either
    it is bound in the RHS, or it appears non-linearly in the LHS.

    The {!const:TEnv(te,ar)} constructor corresponds to a form of metavariable
    [te], with an associated environment [ar]. When it is used in the RHS of a
    rewriting rule, the metavariable [te] must be bound. When a rewriting rule
    applies, the metavariables that are bound in the RHS are substituted using
    an environment that was constructed during the matching of the LHS. *)

(** Representation of a constant or function symbol. *)
 and sym =
  { sym_name  : string
  (** Name of the symbol. *)
  ; sym_type  : term ref
  (** Type of the symbol. *)
  ; sym_path  : Files.module_path
  (** Module in which it is defined. *)
  ; sym_def   : term option ref
  (** Definition of the symbol. *)
  ; sym_rules : rule list ref
  (** Rewriting rules for the symbol. *)
  ; sym_mode  : sym_mode
  (** Tells what kind of symbol it is. *) }

(** Possible symbol modes. *)
 and sym_mode =
  | Const (** Constant symbol (no rewriting rule).          *)
  | Defin (** Symbol has a definition (or rewriting rules). *)
  | Injec (** Same as [Defin], but is assumed injective.    *)

(** The {!recfield:sym_type} field contains a reference for a technical reason
    related to the representation of signatures as binary files (see functions
    {!val:Sign.link} and {!val:Sign.unlink}). This is necessary to ensure that
    two identical symbols are always physically equal, even across signatures.
    It should not be mutated for any other reason.

    The rewriting rules associated to a symbol are stored in the symbol itself
    (in the {!recfield:sym_rules}). Note that a symbol should not be given any
    reduction rule if it is marked as constant (i.e., if {!recfield:sym_const}
    has value [true]), or if it has a definition. *)

(** Representation of a rewriting rule. *)
 and rule =
  { lhs   : term array
  (** Left  hand side.  *)
  ; rhs   : (term_env, term) Bindlib.mbinder
  (** Right hand side.  *)
  ; arity : int
  (** Required number of arguments to be applicable. *)
  ; ctxt  : (string * int) array
  (** Bound higher-order variables names and arities. *) }

(** A rewriting rule is formed of a LHS (left hand side), which is the pattern
    that should be matched for the rule to apply, and a RHS (right hand side),
    which gives the action to perform if the rule applies.

    The LHS (or pattern) of a rewriting rule is always formed of a head symbol
    (on which the rule is defined) applied to a list of arguments. The list of
    arguments is given in {!recfield:lhs}, but the head symbol itself does not
    need to be stored in the rule (rules are contained in symbols). In a rule,
    the {!recfield:arity} field gives the number of arguments contained in the
    LHS. In other words, [r.arity] is always equal to [List.length r.lhs], and
    it gives the minimal number of arguments that is required to match the LHS
    of the rule.

    The RHS (or action) or a rewriting rule is represented by a term, in which
    metavariables of type {!type:term_env} are bound. These metavariables must
    be substituted with an environment of type {!type:term_env array} (that is
    constructed when matching the LHS) to effectively apply the rule.

    During evaluation, we will only try to apply rewriting rules when reducing
    the application of a symbol [s] to a list of argument [ts]. At this point,
    [s.sym_rules] contains every rule [r] that may potentially apply. To check
    if [r] applies, one must match the elements of [r.lhs] with those of [ts],
    while building an environment [ar] of type {!type:term_env array}. In this
    process, a pattern of the form {!const:Patt(Some(i),s,ar)} matched against
    a term [u] intuitively results in [ar.(i)] being set to [u]. If every term
    can be matched against the corresponding pattern, the environment [ar] can
    then be substituted in [r.rhs] with [Bindlib.msubst r.rhs ar] to build the
    result of the application of the rewriting rule. *)

(** Representation of a metavariable for unification. *)
 and meta =
  { meta_key   : int
  (** Unique key of the metavariable. *)
  ; meta_name  : string option
  (** Optional name. *)
  ; meta_type  : term ref
  (** Type of the metavariable. *)
  ; meta_arity : int
  (** Arity of the metavariable (environment size). *)
  ; meta_value : (term, term) Bindlib.mbinder option ref
  (** Definition of the metavariable, if known. *) }

(** A metavariable is represented using a multiple binder, and it can hence be
    instantiated with an open term, provided that its free variables appear in
    the attached environment [ar] in terms of the form {!const:Meta(m,ar}. The
    environment [ar] should only contain (distinct) free variables, as for the
    {!const:Patt(i,s,ar)} constructor. *)

(** {6 Functions related to the handling of metavariables} *)

(** [unfold t] repeatedly unfolds the definition of the top level metavariable
    of [t] until a significant {!type:term} constructor is found. Note that it
    may an uninstantiated metavariable or any other form of term. However, the
    returned term cannot be an instantiated metavariable. In the case where no
    unfolding is required, the returned term is physically equal to [t]. *)
let rec unfold : term -> term = fun t ->
  match t with
  | Meta(m, ar)          ->
      begin
        match !(m.meta_value) with
        | None    -> t
        | Some(b) -> unfold (Bindlib.msubst b ar)
      end
  | TEnv(TE_Some(b), ar) -> unfold (Bindlib.msubst b ar)
  | TRef(r)              ->
      begin
        match !r with
        | None    -> t
        | Some(v) -> unfold v
      end
  | _                    -> t

(** Note that the {!val:unfold} function should (almost always) be used before
    matching over a value of type {!type:term}. *)

(** [unset m] returns [true] if [m] is not instanciated. *)
let unset : meta -> bool = fun m -> !(m.meta_value) = None

(** [get_key ()] returns a fresh metavariable key. *)
let get_key : unit -> int =
  let counter = Pervasives.ref (-1) in
  (fun () -> Pervasives.(incr counter; !counter))

(** [fresh_meta a n] returns a new metavariable of type [a] and arity [n]. *)
let fresh_meta : ?name:string -> term -> int -> meta = fun ?name a n ->
  { meta_key = get_key () ; meta_name = name ; meta_type = ref a
  ; meta_arity = n ; meta_value = ref None}

(** [set_meta m v] sets the value of the metavariable [m] to [v]. *)
let set_meta : meta -> (term, term) Bindlib.mbinder -> unit = fun m v ->
  m.meta_type := Kind; m.meta_value := Some(v)

(** [internal m] returns [true] if [m] is unnamed (i.e., not user-defined). *)
let internal : meta -> bool = fun m -> m.meta_name = None

(** [meta_name m] returns a string representation of [m]. *)
let meta_name : meta -> string = fun m ->
  match m.meta_name with
  | Some(n) -> "?" ^ n
  | None    -> "?" ^ string_of_int m.meta_key

(** [term_of_meta m e] returns a term representing the application of a  fresh
    symbol (named and typed after [m]) to the terms of [e].  The preduced term
    has thus the same type as [Meta(m,e)], and it can be used for checking its
    type instead of that of [Meta(m,e)] directly. *)
let term_of_meta : meta -> term array -> term = fun m e ->
  let s =
    { sym_name  = Printf.sprintf "[%s]" (meta_name m)
    ; sym_type  = ref !(m.meta_type)
    ; sym_path  = []
    ; sym_def   = ref None
    ; sym_rules = ref []
    ; sym_mode  = Const }
  in
  let s = Symb(s, Alias("#")) in
  if Array.length e = 0 then s else Appl(s,e)

(* NOTE [term_of_meta] must rely on a fresh symbol instead of a fresh variable
   as otherwise we would need to polute the typing context with variables that
   created metavariables should not be allowed to use. *)

(** {6 Type synonyms and basic functions (related to {!module:Bindlib})} *)

(** A short name for the binding of a term in a term. *)
type tbinder = (term, term) Bindlib.binder

(** A short name for the type of a free term variable. *)
type tvar = term Bindlib.var

(** A short name for the type of a term in a {!type:Bindlib.box}. *)
type tbox = term Bindlib.box

(** A short name for the type of a free {!type:term_env} variable. *)
type tevar = term_env Bindlib.var

(** A short name for the type of a boxed {!type:term_env}. *)
type tebox = term_env Bindlib.box

(** [mkfree x] injects the [Bindlib] variable [x] in a term. *)
let mkfree : tvar -> term = fun x -> Vari(x)

(** [te_mkfree x] injects the [Bindlib] variable [x] in a {!type:term_env}. *)
let te_mkfree : tevar -> term_env = fun x -> TE_Vari(x)

let unbind b = let (_,b) = Bindlib.unbind b in b
let unbind2 b1 b2 = let (_,b1,b2) = Bindlib.unbind2 b1 b2 in (b1,b2)

(** {6 Smart constructors and lifting (related to {!module:Bindlib})} *)

(** [_Vari x] injects the free variable [x] into the {!type:tbox} type so that
    it may be available for binding. *)
let _Vari : tvar -> tbox = Bindlib.box_var

(** [_Type] injects the constructor [Type] into the {!type:tbox} type. *)
let _Type : tbox = Bindlib.box Type

(** [_Kind] injects the constructor [Kind] into the {!type:tbox} type. *)
let _Kind : tbox = Bindlib.box Kind

(** [_Symb s] injects the constructor [Symb(s)] into the {!type:tbox} type. As
    symbols are closed object they do not require lifting. *)
let _Symb : sym -> pp_hint -> tbox = fun s h ->
  Bindlib.box (Symb(s,h))

(** [_Appl t args] lifts an application node to the {!type:tbox} type, given a
    boxed term [t] and an array of boxed arguments [args]. *)
let _Appl : tbox -> tbox array -> tbox = fun t args ->
  let fn t args =
    if Array.length args = 0 then t else
    match unfold t with
    | Appl(t,a) -> Appl(t, Array.append a args)
    | t         -> Appl(t, args)
  in
  Bindlib.box_apply2 fn t (Bindlib.box_array args)

(** [_Prod a b] lifts a dependent product node to the {!type:tbox} type, given
    a boxed term [a] for the domain of the product, and a boxed binder [b] for
    its codomain. *)
let _Prod : tbox -> tbinder Bindlib.box -> tbox =
  Bindlib.box_apply2 (fun a b -> Prod(a,b))

let _Impl : tbox -> tbox -> tbox =
  let dummy = Bindlib.new_var mkfree "_" in
  fun a b -> _Prod a (Bindlib.bind_var dummy b)

(** [_Abst a t] lifts an abstraction node to the {!type:tbox}  type,  given  a
    boxed term [a] for the domain type, and a boxed binder [t]. *)
let _Abst : tbox -> tbinder Bindlib.box -> tbox =
  Bindlib.box_apply2 (fun a t -> Abst(a,t))

(** [_Meta m ar] lifts the metavariable [m] to the {!type:tbox} type given its
    environment [ar]. As for symbols in {!val:_Symb}, metavariables are closed
    objects so they do not require lifting. *)
let _Meta : meta -> tbox array -> tbox = fun u ar ->
  Bindlib.box_apply (fun ar -> Meta(u,ar)) (Bindlib.box_array ar)

(** [_Patt i n ar] lifts a pattern variable to the {!type:tbox} type. *)
let _Patt : int option -> string -> tbox array -> tbox = fun i n ar ->
  Bindlib.box_apply (fun ar -> Patt(i,n,ar)) (Bindlib.box_array ar)

(** [_TEnv te ar] lifts a term environment to the {!type:tbox} type. *)
let _TEnv : tebox -> tbox array -> tbox = fun te ar ->
  Bindlib.box_apply2 (fun te ar -> TEnv(te,ar)) te (Bindlib.box_array ar)

(** [_Wild] injects the constructor [Wild] into the {!type:tbox} type. *)
let _Wild : tbox = Bindlib.box Wild

(** [_TRef r] injects the constructor [TRef(r)] into the {!type:tbox} type. It
    should be the case that [!r] is [None]. *)
let _TRef : term option ref -> tbox = fun r ->
  Bindlib.box (TRef(r))

(** [lift t] lifts the {!type:term} [t] to the {!type:tbox} type. This has the
    effect of gathering its free variables, making them available for binding.
    Bound variable names are automatically updated in the process. *)
let rec lift : term -> tbox = fun t ->
  let lift_term_env te =
    match te with
    | TE_Vari(x) -> Bindlib.box_var x
    | _          -> Bindlib.box te (* closed objects *)
  in
  match unfold t with
  | Vari(x)     -> _Vari x
  | Type        -> _Type
  | Kind        -> _Kind
  | Symb(s,h)   -> _Symb s h
  | Prod(a,b)   -> _Prod (lift a) (Bindlib.box_binder lift b)
  | Abst(a,t)   -> _Abst (lift a) (Bindlib.box_binder lift t)
  | Appl(t,a)   -> _Appl (lift t) (Array.map lift a)
  | Meta(r,m)   -> _Meta r (Array.map lift m)
  | Patt(i,n,m) -> _Patt i n (Array.map lift m)
  | TEnv(te,m)  -> _TEnv (lift_term_env te) (Array.map lift m)
  | Wild        -> _Wild
  | TRef(r)     -> _TRef r

(** [cleanup t] builds a copy of the {!type:term} [t] where every instantiated
    metavariable has been removed (collapsed), and the name of bound variables
    have been updated. *)
let cleanup : term -> term = fun t -> Bindlib.unbox (lift t)
