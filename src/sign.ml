(** Signature for symbols. *)

open Extra
open Timed
open Console
open Files
open Terms
open Syntax
open Pos

(** Representation of a signature. It roughly corresponds to a set of symbols,
    defined in a single module (or file). *)
type t =
  { sign_symbols  : (sym * Pos.popt) StrMap.t ref
  ; sign_path     : module_path
  ; sign_deps     : (string * rule) list PathMap.t ref
  ; sign_builtins : (sym * pp_hint) StrMap.t ref
  ; sign_binops   : (sym * binop) StrMap.t ref }

(* NOTE the [deps] field contains a hashtable binding the [module_path] of the
   external modules on which the current signature depends to an association
   list. This association list then maps definable symbols of the external
   module to additional reduction rules defined in the current signature. *)

(** [create path] creates an empty signature with module path [path]. *)
let create : module_path -> t = fun sign_path ->
  { sign_path; sign_symbols = ref StrMap.empty; sign_deps = ref PathMap.empty
  ; sign_builtins = ref StrMap.empty; sign_binops = ref StrMap.empty }

(** [find sign name] finds the symbol named [name] in [sign] if it exists, and
    raises the [Not_found] exception otherwise. *)
let find : t -> string -> sym =
  fun sign name -> fst (StrMap.find name !(sign.sign_symbols))

(** [mem sign name] checks whether a symbol named [name] exists in [sign]. *)
let mem : t -> string -> bool =
  fun sign name -> StrMap.mem name !(sign.sign_symbols)

(** [loaded] stores the signatures of the known (already compiled) modules. An
    important invariant is that all the occurrences of a symbol are physically
    equal (even across different signatures). In particular, this requires the
    objects to be copied when loading an object file. *)
let loaded : t PathMap.t ref = ref PathMap.empty

(** [loading] contains the [module_path] of the signatures (or files) that are
    being processed. They are stored in a stack due to dependencies. Note that
    the topmost element corresponds to the current module.  If a [module_path]
    appears twice in the stack, then there is a circular dependency. *)
let loading : module_path list ref = ref []

(** [current_sign ()] returns the current signature. *)
let current_sign () =
  let mp =
    match !loading with
    | mp :: _ -> mp
    | []      -> assert false
  in
  PathMap.find mp !loaded

(** [link sign] establishes physical links to the external symbols. *)
let link : t -> unit = fun sign ->
  let rec link_term t =
    let link_binder b =
      let (x,t) = Bindlib.unbind b in
      Bindlib.unbox (Bindlib.bind_var x (lift (link_term t)))
    in
    match unfold t with
    | Vari(_)     -> t
    | Type        -> t
    | Kind        -> t
    | Symb(s,h)   -> Symb(link_symb s, h)
    | Prod(a,b)   -> Prod(link_term a, link_binder b)
    | Abst(a,t)   -> Abst(link_term a, link_binder t)
    | Appl(t,a)   -> Appl(link_term t, Array.map link_term a)
    | Meta(_,_)   -> assert false
    | Patt(i,n,m) -> Patt(i, n, Array.map link_term m)
    | TEnv(t,m)   -> TEnv(t, Array.map link_term m)
    | Wild        -> t
    | TRef(_)     -> t
  and link_rule r =
    let lhs = Array.map link_term r.lhs in
    let (xs, rhs) = Bindlib.unmbind r.rhs in
    let rhs = lift (link_term rhs) in
    let rhs = Bindlib.unbox (Bindlib.bind_mvar xs rhs) in
    {r with lhs ; rhs}
  and link_symb s =
    if s.sym_path = sign.sign_path then s else
    try
      let sign = PathMap.find s.sym_path !loaded in
      try find sign s.sym_name with Not_found -> assert false
    with Not_found -> assert false
  in
  let fn _ (s,_) =
    s.sym_type  := link_term !(s.sym_type);
    s.sym_def   := Option.map link_term !(s.sym_def);
    s.sym_rules := List.map link_rule !(s.sym_rules)
  in
  StrMap.iter fn !(sign.sign_symbols);
  let gn path ls =
    let sign =
      try PathMap.find path !loaded
      with Not_found -> assert false
    in
    let h (n, r) =
      let r = link_rule r in
      let s = find sign n in
      s.sym_rules := !(s.sym_rules) @ [r]
    in
    List.iter h ls
  in
  PathMap.iter gn !(sign.sign_deps);
  let hn (s,h) = (link_symb s, h) in
  sign.sign_builtins := StrMap.map hn !(sign.sign_builtins);
  sign.sign_binops := StrMap.map hn !(sign.sign_binops)

(** [unlink sign] removes references to external symbols (and thus signatures)
    in the signature [sign]. This function is used to minimize the size of our
    object files, by preventing a recursive inclusion of all the dependencies.
    Note however that [unlink] processes [sign] in place, which means that the
    signature is invalidated in the process. *)
let unlink : t -> unit = fun sign ->
  let unlink_sym s =
    if s.sym_path <> sign.sign_path then
      (s.sym_type := Kind; s.sym_rules := [])
  in
  let rec unlink_term t =
    let unlink_binder b = unlink_term (snd (Bindlib.unbind b)) in
    let unlink_term_env t =
      match t with
      | TE_Vari(_) -> ()
      | _          -> assert false (* Should not happen, matching-specific. *)
    in
    match unfold t with
    | Vari(_)      -> ()
    | Type         -> ()
    | Kind         -> ()
    | Symb(s,_)    -> unlink_sym s
    | Prod(a,b)    -> unlink_term a; unlink_binder b
    | Abst(a,t)    -> unlink_term a; unlink_binder t
    | Appl(t,a)    -> unlink_term t; Array.iter unlink_term a
    | Meta(_,_)    -> assert false (* Should not happen, uninstantiated. *)
    | Patt(_,_,_)  -> () (* The environment only contains variables. *)
    | TEnv(t,m)    -> unlink_term_env t; Array.iter unlink_term m
    | Wild         -> ()
    | TRef(_)      -> ()
  and unlink_rule r =
    Array.iter unlink_term r.lhs;
    let (_, rhs) = Bindlib.unmbind r.rhs in
    unlink_term rhs
  in
  let fn _ (s,_) =
    unlink_term !(s.sym_type);
    Option.iter unlink_term !(s.sym_def);
    List.iter unlink_rule !(s.sym_rules)
  in
  StrMap.iter fn !(sign.sign_symbols);
  let gn _ ls = List.iter (fun (_, r) -> unlink_rule r) ls in
  PathMap.iter gn !(sign.sign_deps);
  StrMap.iter (fun _ (s,_) -> unlink_sym s) !(sign.sign_builtins);
  StrMap.iter (fun _ (s,_) -> unlink_sym s) !(sign.sign_binops)

(** [add_symbol sign mode name a] creates a fresh symbol with the name  [name]
    (which should not already be used in [sign]) and with the type [a], in the
    signature [sign]. The created symbol is also returned. *)
let add_symbol : t -> sym_mode -> strloc -> term -> sym = fun sign mode s a ->
  (* Check for metavariables in the symbol type. *)
  let nb = List.length (Basics.get_metas a) in
  if nb > 0 then
    fatal s.pos "The type symbol [%s] contains [%i] metavariables" s.elt nb;
  (* Add the symbol. *)
  let sym =
    { sym_name = s.elt ; sym_type = ref a ; sym_path = sign.sign_path
    ; sym_def = ref None ; sym_rules = ref [] ; sym_mode = mode }
  in
  sign.sign_symbols := StrMap.add s.elt (sym, s.pos) !(sign.sign_symbols); sym

(** [is_inj s] tells whether the symbol is injective. *)
let is_inj : sym -> bool = fun s -> s.sym_mode <> Defin

(** [write sign file] writes the signature [sign] to the file [fname]. *)
let write : t -> string -> unit = fun sign fname ->
  match Unix.fork () with
  | 0 -> let oc = open_out fname in
         unlink sign; Marshal.to_channel oc sign [Marshal.Closures];
         close_out oc; exit 0
  | i -> ignore (Unix.waitpid [] i)

(* NOTE [Unix.fork] is used to safely [unlink] and write an object file, while
   preserving a valid copy of the written signature in the parent process. *)

(** [read fname] reads a signature from the object file [fname]. Note that the
    file can only be read properly if it was build with the same binary as the
    one being evaluated. If this is not the case, the program gracefully fails
    with an error message. *)
let read : string -> t = fun fname ->
  let ic = open_in fname in
  let sign =
    try
      let sign = Marshal.from_channel ic in
      close_in ic; sign
    with Failure _ ->
      close_in ic;
      fatal_no_pos "File [%s] is incompatible with current binary...\n" fname
  in
  (* Timed references need reset after unmarshaling (see [Timed] doc). *)
  let reset_timed_refs sign =
    unsafe_reset sign.sign_symbols;
    unsafe_reset sign.sign_deps;
    unsafe_reset sign.sign_builtins;
    unsafe_reset sign.sign_binops;
    let rec reset_term t =
      let reset_binder b = reset_term (snd (Bindlib.unbind b)) in
      match unfold t with
      | Vari(_)     -> ()
      | Type        -> ()
      | Kind        -> ()
      | Symb(s,_)   -> shallow_reset_sym s
      | Prod(a,b)   -> reset_term a; reset_binder b
      | Abst(a,t)   -> reset_term a; reset_binder t
      | Appl(t,a)   -> reset_term t; Array.iter reset_term a
      | Meta(_,_)   -> assert false
      | Patt(_,_,m) -> Array.iter reset_term m
      | TEnv(_,m)   -> Array.iter reset_term m
      | Wild        -> ()
      | TRef(r)     -> unsafe_reset r; Option.iter reset_term !r
    and reset_rule r =
      Array.iter reset_term r.lhs;
      reset_term (snd (Bindlib.unmbind r.rhs))
    and shallow_reset_sym s =
      unsafe_reset s.sym_type;
      unsafe_reset s.sym_def;
      unsafe_reset s.sym_rules
    in
    let reset_sym s =
      shallow_reset_sym s;
      reset_term !(s.sym_type);
      Option.iter reset_term !(s.sym_def);
      List.iter reset_rule !(s.sym_rules)
    in
    StrMap.iter (fun _ (s,_) -> reset_sym s) !(sign.sign_symbols);
    StrMap.iter (fun _ (s,_) -> shallow_reset_sym s) !(sign.sign_binops);
    StrMap.iter (fun _ (s,_) -> shallow_reset_sym s) !(sign.sign_builtins);
    let fn (_,r) = reset_rule r in
    PathMap.iter (fun _ -> List.iter fn) !(sign.sign_deps);
    sign
  in
  reset_timed_refs sign

(* NOTE here, we rely on the fact that a marshaled closure can only be read by
   processes running the same binary as the one that produced it. *)

(** [add_rule sign sym r] adds the new rule [r] to the symbol [sym].  When the
    rule does not correspond to a symbol of signature [sign],  it is stored in
    its dependencies. *)
let add_rule : t -> sym -> rule -> unit = fun sign sym r ->
  sym.sym_rules := !(sym.sym_rules) @ [r];
  if sym.sym_path <> sign.sign_path then
    let m =
      try PathMap.find sym.sym_path !(sign.sign_deps)
      with Not_found -> assert false
    in
    let m = (sym.sym_name, r) :: m in
    sign.sign_deps := PathMap.add sym.sym_path m !(sign.sign_deps)

(** [add_builtin sign name sym] binds the builtin name [name] to [sym] (in the
    signature [sign]). The previous binding, if any, is discarded. *)
let add_builtin : t -> string -> (sym * pp_hint) -> unit = fun sign s sym ->
  sign.sign_builtins := StrMap.add s sym !(sign.sign_builtins)

(** [add_binop sign op sym] binds the binary operator [op] to [sym] in [sign].
    If [op] was previously bound, the previous binding is discarded. *)
let add_binop : t -> string -> (sym * binop) -> unit = fun sign s sym ->
  sign.sign_binops := StrMap.add s sym !(sign.sign_binops)

(** [dependencies sign] returns an association list containing (the transitive
    closure of) the dependencies of the signature [sign].  Note that the order
    of the list gives one possible loading order for the signatures. Note also
    that [sign] itself appears at the end of the list. *)
let rec dependencies : t -> (module_path * t) list = fun sign ->
  (* Recursively compute dependencies for the immediate dependencies. *)
  let fn p _ l = dependencies (PathMap.find p !loaded) :: l in
  let deps = PathMap.fold fn !(sign.sign_deps) [[(sign.sign_path, sign)]] in
  (* Minimize and put everything together. *)
  let rec minimize acc deps =
    let not_here (p,_) =
      let has_p = List.exists (fun (q,_) -> p = q) in
      not (List.exists has_p acc)
    in
    match deps with
    | []      -> List.rev acc
    | d::deps -> minimize ((List.filter not_here d) :: acc) deps
  in
  List.concat (minimize [] deps)
