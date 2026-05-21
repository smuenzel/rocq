(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Jean-Christophe Filliâtre out of names.ml as part of the
   rebuilding of Coq around a purely functional abstract type-checker,
   Aug 1999 *)
(* Miscellaneous extensions, restructurations and bug-fixes by Hugo
   Herbelin and Bruno Barras *)

(* This file defines types and combinators regarding indexes-based and
   names-based contexts *)

(** The modules defined below represent a {e local context}
    as defined by Chapter 4 in the Reference Manual:

    A {e local context} is an ordered list of of {e local declarations}
    of names that we call {e variables}.

    A {e local declaration} of some variable can be either:
    - a {e local assumption}, or
    - a {e local definition}.
*)

open Util
open Names

type ('a,'r) pbinder_annot = { binder_name : 'a; binder_relevance : 'r }

let eq_annot eq eqr {binder_name=na1;binder_relevance=r1} {binder_name=na2;binder_relevance=r2} =
  eq na1 na2 && eqr r1 r2

let hash_annot h {binder_name=n;binder_relevance=r} =
  Hashset.Combine.combinesmall (Sorts.relevance_hash r) (h n)

let map_annot f {binder_name=na;binder_relevance} =
  let na' = f na in
  {binder_name=na';binder_relevance}

let map_annot_relevance fr ({binder_name=na;binder_relevance=r} as a) =
  let r' = fr r in
  if r == r' then a else {binder_name=na;binder_relevance=r'}

let map_annot_relevance_het fr {binder_name=na;binder_relevance=r} =
  let r' = fr r in
  {binder_name=na;binder_relevance=r'}

let make_annot x r = {binder_name=x;binder_relevance=r}

let binder_name x = x.binder_name
let binder_relevance x = x.binder_relevance

let annotR x = make_annot x Sorts.Relevant

let nameR x = annotR (Name x)
let anonR = annotR Anonymous

(** Representation of contexts that can capture anonymous as well as non-anonymous variables.
    Individual declarations are then designated by de Bruijn indexes. *)
module Rel =
struct
  (** Representation of {e local declarations}. *)
  module Declaration =
  struct
    (* local declaration *)
    type ('constr, 'types, 'r) pt =
      | LocalAssum of (Name.t,'r) pbinder_annot * 'types            (** name, type *)
      | LocalDef of (Name.t,'r) pbinder_annot * 'constr * 'types   (** name, value, type *)

    let get_annot = function
      | LocalAssum (na,_) | LocalDef (na,_,_) -> na

    (** Return the name bound by a given declaration. *)
    let get_name x = (get_annot x).binder_name

    (** Return [Some value] for local-declarations and [None] for local-assumptions. *)
    let get_value = function
      | LocalAssum _ -> None
      | LocalDef (_,v,_) -> Some v

    (** Return the type of the name bound by a given declaration. *)
    let get_type = function
      | LocalAssum (_,ty)
      | LocalDef (_,_,ty) -> ty

    let get_relevance x = (get_annot x).binder_relevance

    let set_annot x d =
      if get_annot d == x then d else match d with
      | LocalAssum (_,ty) -> LocalAssum (x, ty)
      | LocalDef (_,v,ty) -> LocalDef (x, v, ty)

    (** Set the name that is bound by a given declaration. *)
    let set_name na = function
      | LocalAssum (x,ty) -> LocalAssum ({x with binder_name=na}, ty)
      | LocalDef (x,v,ty) -> LocalDef ({x with binder_name=na}, v, ty)

    let set_relevance r = function
      | LocalAssum (x,ty) -> LocalAssum ({x with binder_relevance=r}, ty)
      | LocalDef (x,v,ty) -> LocalDef ({x with binder_relevance=r}, v, ty)

    (** Set the type of the bound variable in a given declaration. *)
    let set_type ty = function
      | LocalAssum (na,_) -> LocalAssum (na, ty)
      | LocalDef (na,v,_) -> LocalDef (na, v, ty)

    (** Return [true] iff a given declaration is a local assumption. *)
    let is_local_assum = function
      | LocalAssum _ -> true
      | LocalDef _ -> false

    (** Return [true] iff a given declaration is a local definition. *)
    let is_local_def = function
      | LocalAssum _ -> false
      | LocalDef _ -> true

    (** Check whether any term in a given declaration satisfies a given predicate. *)
    let exists f = function
      | LocalAssum (_, ty) -> f ty
      | LocalDef (_, v, ty) -> f v || f ty

      (** Check whether all terms in a given declaration satisfy a given predicate. *)
    let for_all f = function
      | LocalAssum (_, ty) -> f ty
      | LocalDef (_, v, ty) -> f v && f ty

    (** Check whether the two given declarations are equal. *)
    let equal eqr eq decl1 decl2 =
      match decl1, decl2 with
      | LocalAssum (n1,ty1), LocalAssum (n2, ty2) ->
          eq_annot Name.equal eqr n1 n2 && eq ty1 ty2
      | LocalDef (n1,v1,ty1), LocalDef (n2,v2,ty2) ->
          eq_annot Name.equal eqr n1 n2 && eq v1 v2 && eq ty1 ty2
      | _ ->
          false

    (** Map the name bound by a given declaration. *)
    let map_name f x =
      let na = get_name x in
      let na' = f na in
      if na == na' then x else set_name na' x

    let map_relevance f x =
      let r = get_relevance x in
      let r' = f r in
      if r == r' then x else set_relevance r' x

    (** For local assumptions, this function returns the original local assumptions.
        For local definitions, this function maps the value in the local definition. *)
    let map_value f = function
      | LocalAssum _ as decl -> decl
      | LocalDef (na, v, t) as decl ->
          let v' = f v in
          if v == v' then decl else LocalDef (na, v', t)

    (** Map the type of the name bound by a given declaration. *)
    let map_type f = function
      | LocalAssum (na, ty) as decl ->
          let ty' = f ty in
          if ty == ty' then decl else LocalAssum (na, ty')
      | LocalDef (na, v, ty) as decl ->
          let ty' = f ty in
          if ty == ty' then decl else LocalDef (na, v, ty')

    (** Map all terms in a given declaration. *)
    let map_constr f = function
      | LocalAssum (na, ty) as decl ->
          let ty' = f ty in
          if ty == ty' then decl else LocalAssum (na, ty')
      | LocalDef (na, v, ty) as decl ->
          let v' = f v in
          let ty' = f ty in
          if v == v' && ty == ty' then decl else LocalDef (na, v', ty')

    (** Map all terms in a given declaration. *)
    let map_constr_with_relevance g f = function
      | LocalAssum (na, ty) as decl ->
          let na' = map_annot_relevance g na in
          let ty' = f ty in
          if na == na' && ty == ty' then decl else LocalAssum (na', ty')
      | LocalDef (na, v, ty) as decl ->
          let na' = map_annot_relevance g na in
          let v' = f v in
          let ty' = f ty in
          if na == na' && v == v' && ty == ty' then decl else LocalDef (na', v', ty')

    let map_constr_het fr f = function
      | LocalAssum (na, ty) ->
          let ty' = f ty in
          LocalAssum (map_annot_relevance_het fr na, ty')
      | LocalDef (na, v, ty) ->
          let v' = f v in
          let ty' = f ty in
          LocalDef (map_annot_relevance_het fr na, v', ty')

    (** Perform a given action on all terms in a given declaration. *)
    let iter_constr f = function
      | LocalAssum (_,ty) -> f ty
      | LocalDef (_,v,ty) -> f v; f ty

    (** Reduce all terms in a given declaration to a single value. *)
    let fold_constr f decl acc =
      match decl with
      | LocalAssum (_n,ty) -> f ty acc
      | LocalDef (_n,v,ty) -> f ty (f v acc)

    let to_tuple = function
      | LocalAssum (na, ty) -> na, None, ty
      | LocalDef (na, v, ty) -> na, Some v, ty

    let drop_body = function
      | LocalAssum _ as d -> d
      | LocalDef (na, _v, ty) -> LocalAssum (na, ty)

  end

  (** Rel-context is represented as a list of declarations.
      Inner-most declarations are at the beginning of the list.
      Outer-most declarations are at the end of the list. *)
  type ('constr, 'types, 'r) pt = int * ('constr, 'types, 'r) Declaration.pt list

  let to_list (_, ctx) = ctx
  let of_list ctx = List.length ctx, ctx

  let of_list_map f l = List.length l, List.map f l

  let to_list_map f (_, ctx) = List.map f ctx
  let to_list_rev_map f (_, ctx) = List.rev_map f ctx

  let to_list_map_i f i (_, ctx) = List.map_i f i ctx

  let to_list_until f (_, ctx) =
    let a, ctx = List.map_until f ctx in
    a, of_list ctx

  let uncons (n, ctx) = match ctx with
  | [] -> None
  | decl :: ctx -> Some (decl, (n - 1, ctx))

  (** empty rel-context *)
  let empty = 0, []

  let is_empty (_, ctx) = List.is_empty ctx

  let init n f = n, List.init n f

  (** Return a new rel-context enriched by with a given inner-most declaration. *)
  let add d (n, ctx) = n+1, d :: ctx

  let append (n1,ctx1) (n2, ctx2) = n1 + n2, ctx1 @ ctx2

  let rev (n, ctx) = n, List.rev ctx

  let firstn n (n',ctx) = min n n', List.firstn n ctx

  let skipn n (n', ctx) = n'-n, List.skipn n ctx

  let sep_last (n, ctx) = let d, ctx' = List.sep_last ctx in
    d, (n - 1, ctx')

  let nth (_, ctx) n = List.nth ctx n

  (** Return the number of {e local declarations} in a given rel-context. *)
  let length (n,_) = n

  (** Return the number of {e local assumptions} in a given rel-context. *)
  let nhyps (_, ctx) =
    let open Declaration in
    let rec nhyps acc = function
      | [] -> acc
      | LocalAssum _ :: hyps -> nhyps (succ acc) hyps
      | LocalDef _ :: hyps -> nhyps acc hyps
    in
    nhyps 0 ctx

  (** Return a declaration designated by a given de Bruijn index.
      @raise Not_found if the designated de Bruijn index is not present in the designated rel-context. *)
  let rec lookup n ctx =
    match n, ctx with
    | 1, decl :: _ -> decl
    | n, _ :: sign -> lookup (n-1) sign
    | _, []        -> raise Not_found

  let lookup n (_, ctx) = lookup n ctx

  (** Check whether given two rel-contexts are equal. *)
  let equal eqr eq (n1, l1) (n2, l2) = n1 = n2 && List.equal (fun c -> Declaration.equal eqr eq c) l1 l2

  (** Map all terms in a given rel-context. *)
  let map f (n, ctx) = n, List.Smart.map (Declaration.map_constr f) ctx

  let map_with_relevance g f ((n, ctx) as rctx) = 
    let result = List.Smart.map (Declaration.map_constr_with_relevance g f) ctx in
    if result == ctx then rctx else n, result

  let map_relevance f ((n, ctx) as rctx) =
    let result = List.Smart.map (Declaration.map_relevance f) ctx in
    if result == ctx then rctx else n, result

  let map_het fr f (n, ctx) = n, List.map (Declaration.map_constr_het fr f) ctx

  (** Map all terms in a given rel-context. *)
  let map_with_binders f ((n, ctx) as rctx) =
    let rec aux k = function
      | decl :: ctx as l ->
        let decl' = Declaration.map_constr (f k) decl in
        let ctx' = aux (k-1) ctx in
        if decl == decl' && ctx == ctx' then l else decl' :: ctx'
      | [] -> []
    in
    let result = aux n ctx in
    if result == ctx then rctx else n, result

  let map_decl f (n, ctx) = n, List.map f ctx

  let map_decl_i f i (n, ctx) = n, List.map_i f i ctx

  let map_decl_smart f ((n, ctx) as rctx) =
    let result = List.Smart.map f ctx in
    if result == ctx then rctx else n, result

  let map_decl2 f l (n, ctx) = n, List.map2 f l ctx


  let filter f (_, ctx) = List.filter f ctx |> of_list

  let for_all f (_, ctx) = List.for_all f ctx

  let for_all_i f i (_, ctx) = List.for_all_i f i ctx

  let exists f (_, ctx) = List.exists f ctx

  (** Perform a given action on every declaration in a given rel-context. *)
  let iter f (_, ctx) = List.iter (Declaration.iter_constr f) ctx

  let iter_decl f (_, ctx) = List.iter f ctx

  let count f (_, ctx) = List.count f ctx

  (** Reduce all terms in a given rel-context to a single value.
      Innermost declarations are processed first. *)
  let fold_inside f ~init (_, ctx) = List.fold_left f init ctx

  let fold_inside_i f i ~init (_, ctx) = List.fold_left_i f i init ctx

  (** Reduce all terms in a given rel-context to a single value.
      Outermost declarations are processed first. *)
  let fold_outside f (_, l) ~init = List.fold_right f l init

  let fold_outside_map f (n, l) ~init =
    let l, result = List.fold_right_map f l init in
    (n, l), result

  let fold_outside2 f l' (_, l) ~init = List.fold_right2 f l' l init

  (** Return the set of all named variables bound in a given rel-context. *)
  let to_vars (_, l) =
    List.fold_left (fun accu decl ->
        match Declaration.get_name decl with
        | Name id -> Id.Set.add id accu
        | Anonymous -> accu)
      Id.Set.empty l

  (** Map a given rel-context to a list where each {e local definition} is mapped to [true]
      and each {e local assumption} is mapped to [false]. *)
  let to_tags (_, l) =
    let rec aux l = function
      | [] -> l
      | Declaration.LocalDef _ :: ctx -> aux (true::l) ctx
      | Declaration.LocalAssum _ :: ctx -> aux (false::l) ctx
    in aux [] l

  let drop_bodies l = map_decl_smart Declaration.drop_body l

  let chop n (n', l) =
    let l1, l2 = List.chop n l in
    (n, l1), (n' - n, l2)

  (** Split a context so that the second part contains [n]
      [LocalAssum], keeping all [LocalDef] in the middle in the first part *)
  let chop_nhyps n_local_assum (n_total, l) =
    let rec aux acc_size l' = function
      | (0, l) -> ((acc_size, List.rev l'), (n_total - acc_size, l))
      | (n, (Declaration.LocalDef _ as h) :: l) -> aux (acc_size + 1) (h::l') (n, l)
      | (n, (Declaration.LocalAssum _ as h) :: l) -> aux (acc_size + 1) (h::l') (n-1, l)
      | (_, []) -> CErrors.anomaly (Pp.str "chop_nhyps: not enough hypotheses.")
    in aux 0 [] (n_local_assum,l)

  (** [extended_list n Γ] builds an instance [args] such that [Γ,Δ ⊢ args:Γ]
      with n = |Δ| and with the {e local definitions} of [Γ] skipped in
      [args]. Example: for [x:T, y:=c, z:U] and [n]=2, it gives [Rel 5, Rel 3]. *)
  let to_extended_list mk n (_, l) =
    let rec reln l p = function
      | Declaration.LocalAssum _ :: hyps -> reln (mk (n+p) :: l) (p+1) hyps
      | Declaration.LocalDef _ :: hyps -> reln l (p+1) hyps
      | [] -> l
    in
    reln [] 1 l

  (** [extended_vect n Γ] does the same, returning instead an array. *)
  let to_extended_vect mk n hyps = Array.of_list (to_extended_list mk n hyps)

  (** Consistency with terminology in Named *)
  let instance = to_extended_vect
  let instance_list = to_extended_list
end

(** This module represents contexts that can capture non-anonymous variables.
    Individual declarations are then designated by the identifiers they bind. *)
module Named =
struct
  (** Representation of {e local declarations}. *)
  module Declaration =
  struct
    (** local declaration *)
    type ('constr, 'types, 'r) pt =
      | LocalAssum of (Id.t,'r) pbinder_annot * 'types             (** identifier, type *)
      | LocalDef of (Id.t,'r) pbinder_annot * 'constr * 'types    (** identifier, value, type *)

    let get_annot = function
      | LocalAssum (na,_) | LocalDef (na,_,_) -> na

    (** Return the identifier bound by a given declaration. *)
    let get_id x = (get_annot x).binder_name

    (** Return [Some value] for local-declarations and [None] for local-assumptions. *)
    let get_value = function
      | LocalAssum _ -> None
      | LocalDef (_,v,_) -> Some v

    (** Return the type of the name bound by a given declaration. *)
    let get_type = function
      | LocalAssum (_,ty)
      | LocalDef (_,_,ty) -> ty

    let get_relevance x = (get_annot x).binder_relevance

    (** Set the identifier that is bound by a given declaration. *)
    let set_id id =
      let set x = {x with binder_name = id} in
      function
      | LocalAssum (x,ty) -> LocalAssum (set x, ty)
      | LocalDef (x, v, ty) -> LocalDef (set x, v, ty)

    (** Set the type of the bound variable in a given declaration. *)
    let set_type ty = function
      | LocalAssum (id,_) -> LocalAssum (id, ty)
      | LocalDef (id,v,_) -> LocalDef (id, v, ty)

    (** Return [true] iff a given declaration is a local assumption. *)
    let is_local_assum = function
      | LocalAssum _ -> true
      | LocalDef _ -> false

    (** Return [true] iff a given declaration is a local definition. *)
    let is_local_def = function
      | LocalDef _ -> true
      | LocalAssum _ -> false

    (** Check whether any term in a given declaration satisfies a given predicate. *)
    let exists f = function
      | LocalAssum (_, ty) -> f ty
      | LocalDef (_, v, ty) -> f v || f ty

    (** Check whether all terms in a given declaration satisfy a given predicate. *)
    let for_all f = function
      | LocalAssum (_, ty) -> f ty
      | LocalDef (_, v, ty) -> f v && f ty

    (** Check whether the two given declarations are equal. *)
    let equal eqr eq decl1 decl2 =
      match decl1, decl2 with
      | LocalAssum (id1, ty1), LocalAssum (id2, ty2) ->
          eq_annot Id.equal eqr id1 id2 && eq ty1 ty2
      | LocalDef (id1, v1, ty1), LocalDef (id2, v2, ty2) ->
          eq_annot Id.equal eqr id1 id2 && eq v1 v2 && eq ty1 ty2
      | _ ->
          false

    (** Map the identifier bound by a given declaration. *)
    let map_id f x =
      let id = get_id x in
      let id' = f id in
      if id == id' then x else set_id id' x

    (** Map the relevance *)
    let map_relevance f = function
      | LocalAssum (id, ty) as decl ->
          let id' = map_annot_relevance f id in
          if id == id' then decl else LocalAssum (id', ty)
      | LocalDef (id, v, ty) as decl ->
          let id' = map_annot_relevance f id in
          if id == id' then decl else LocalDef (id', v, ty)

    (** For local assumptions, this function returns the original local assumptions.
        For local definitions, this function maps the value in the local definition. *)
    let map_value f = function
      | LocalAssum _ as decl -> decl
      | LocalDef (na, v, t) as decl ->
          let v' = f v in
          if v == v' then decl else LocalDef (na, v', t)

    (** Map the type of the name bound by a given declaration. *)
    let map_type f = function
      | LocalAssum (id, ty) as decl ->
          let ty' = f ty in
          if ty == ty' then decl else LocalAssum (id, ty')
      | LocalDef (id, v, ty) as decl ->
          let ty' = f ty in
          if ty == ty' then decl else LocalDef (id, v, ty')

    (** Map all terms in a given declaration. *)
    let map_constr f = function
      | LocalAssum (id, ty) as decl ->
          let ty' = f ty in
          if ty == ty' then decl else LocalAssum (id, ty')
      | LocalDef (id, v, ty) as decl ->
          let v' = f v in
          let ty' = f ty in
          if v == v' && ty == ty' then decl else LocalDef (id, v', ty')

    (** Map all terms in a given declaration. *)
    let map_constr_with_relevance g f = function
      | LocalAssum (id, ty) as decl ->
          let id' = map_annot_relevance g id in
          let ty' = f ty in
          if id == id' && ty == ty' then decl else LocalAssum (id', ty')
      | LocalDef (id, v, ty) as decl ->
          let id' = map_annot_relevance g id in
          let v' = f v in
          let ty' = f ty in
          if id == id' && v == v' && ty == ty' then decl else LocalDef (id', v', ty')

    let map_constr_het fr f = function
      | LocalAssum (id, ty) ->
          let ty' = f ty in
          LocalAssum (map_annot_relevance_het fr id, ty')
      | LocalDef (id, v, ty) ->
          let v' = f v in
          let ty' = f ty in
          LocalDef (map_annot_relevance_het fr id, v', ty')

    (** Perform a given action on all terms in a given declaration. *)
    let iter_constr f = function
      | LocalAssum (_, ty) -> f ty
      | LocalDef (_, v, ty) -> f v; f ty

    (** Reduce all terms in a given declaration to a single value. *)
    let fold_constr f decl a =
      match decl with
      | LocalAssum (_, ty) -> f ty a
      | LocalDef (_, v, ty) -> a |> f v |> f ty

    let to_tuple = function
      | LocalAssum (id, ty) -> id, None, ty
      | LocalDef (id, v, ty) -> id, Some v, ty

    let of_tuple = function
      | id, None, ty -> LocalAssum (id, ty)
      | id, Some v, ty -> LocalDef (id, v, ty)

    let drop_body = function
      | LocalAssum _ as d -> d
      | LocalDef (id, _v, ty) -> LocalAssum (id, ty)

    let of_rel_decl f = function
      | Rel.Declaration.LocalAssum (na,t) ->
        LocalAssum (map_annot f na, t)
      | Rel.Declaration.LocalDef (na,v,t) ->
        LocalDef (map_annot f na, v, t)

    let to_rel_decl =
      let name x = {binder_name=Name x.binder_name;binder_relevance=x.binder_relevance} in
      function
      | LocalAssum (id,t) ->
          Rel.Declaration.LocalAssum (name id, t)
      | LocalDef (id,v,t) ->
          Rel.Declaration.LocalDef (name id,v,t)
  end

  (** Named-context is represented as a list of declarations.
      Inner-most declarations are at the beginning of the list.
      Outer-most declarations are at the end of the list. *)
  type ('constr, 'types, 'r) pt = int * ('constr, 'types, 'r) Declaration.pt list

  let to_list (_, ctx) = ctx
  let of_list ctx = List.length ctx, ctx

  let of_list_map f l = List.length l, List.map f l

  let to_list_map f (_, ctx) = List.map f ctx
  let to_list_rev_map f (_, ctx) = List.rev_map f ctx

  let to_list_rev (_, ctx) = List.rev ctx

  let to_list_map_i f i (_, ctx) = List.map_i f i ctx

  let to_list_until f (_, ctx) =
    let a, ctx = List.map_until f ctx in
    a, of_list ctx

  let uncons (n, ctx) = match ctx with
  | [] -> None
  | decl :: ctx -> Some (decl, (n - 1, ctx))

  (** empty named-context *)
  let empty = 0, []

  let is_empty (_, ctx) = List.is_empty ctx

  let init n f = n, List.init n f

  (** Return a new named-context enriched by with a given inner-most declaration. *)
  let add d (n, ctx) = n+1, d :: ctx

  let append (n1, ctx1) (n2, ctx2) = n1 + n2, ctx1 @ ctx2

  let rev (n, ctx) = n, List.rev ctx

  let firstn n (n', ctx) = min n n', List.firstn n ctx

  let skipn n (n', ctx) = n' - n, List.skipn n ctx

  let sep_last (n, ctx) = let d, ctx' = List.sep_last ctx in
    d, (n - 1, ctx')

  let nth (_, ctx) n = List.nth ctx n

  let hd (_, ctx) = match ctx with
  | [] -> CErrors.anomaly (Pp.str "hd: empty named context")
  | d :: _ -> d

  (** Return the number of {e local declarations} in a given named-context. *)
  let length (n, _) = n

  (** Return the number of {e local assumptions} in a given named-context. *)
  let nhyps (_, ctx) =
    let open Declaration in
    List.count is_local_assum ctx

  (** Return a declaration designated by a given identifier
      @raise Not_found if the designated identifier is not present in the designated named-context. *)
  let rec lookup id ctx =
    match ctx with
    | decl :: _ when Id.equal id (Declaration.get_id decl) -> decl
    | _ :: sign -> lookup id sign
    | [] -> raise Not_found

  let lookup id (_, ctx) = lookup id ctx

  (** Check whether given two named-contexts are equal. *)
  let equal eqr eq (n1, l1) (n2, l2) = n1 = n2 && List.equal (fun c -> Declaration.equal eqr eq c) l1 l2

  (** Map all terms in a given named-context. *)
  let map f (n, ctx) = n, List.Smart.map (Declaration.map_constr f) ctx

  let map_with_relevance g f ((n, ctx) as rctx) =
    let result = List.Smart.map (Declaration.map_constr_with_relevance g f) ctx in
    if result == ctx then rctx else n, result

  let map_relevance f ((n, ctx) as rctx) =
    let result = List.Smart.map (Declaration.map_relevance f) ctx in
    if result == ctx then rctx else n, result

  let map_het fr f (n, ctx) = n, List.map (Declaration.map_constr_het fr f) ctx

  let map_with_binders f ((n, ctx) as rctx) =
    let rec aux k = function
      | decl :: ctx as l ->
        let decl' = Declaration.map_constr (f k) decl in
        let ctx' = aux (k-1) ctx in
        if decl == decl' && ctx == ctx' then l else decl' :: ctx'
      | [] -> []
    in
    let result = aux n ctx in
    if result == ctx then rctx else n, result

  let map_decl f (n, ctx) = n, List.map f ctx

  let map_decl_i f i (n, ctx) = n, List.map_i f i ctx

  let map_decl_smart f ((n, ctx) as rctx) =
    let result = List.Smart.map f ctx in
    if result == ctx then rctx else n, result

  let map_decl2 f l (n, ctx) = n, List.map2 f l ctx

  let filter f (_, ctx) = List.filter f ctx |> of_list

  let for_all f (_, ctx) = List.for_all f ctx

  let for_all_i f i (_, ctx) = List.for_all_i f i ctx

  let exists f (_, ctx) = List.exists f ctx

  (** Perform a given action on every declaration in a given named-context. *)
  let iter f (_, ctx) = List.iter (Declaration.iter_constr f) ctx

  let iter_decl f (_, ctx) = List.iter f ctx

  let count f (_, ctx) = List.count f ctx

  (** Reduce all terms in a given named-context to a single value.
      Innermost declarations are processed first. *)
  let fold_inside f ~init (_, ctx) = List.fold_left f init ctx

  let fold_inside_i f i ~init (_, ctx) = List.fold_left_i f i init ctx

  (** Reduce all terms in a given named-context to a single value.
      Outermost declarations are processed first. *)
  let fold_outside f (_, l) ~init = List.fold_right f l init

  let fold_outside_map f (n, l) ~init =
    let l, result = List.fold_right_map f l init in
    (n, l), result

  let fold_outside2 f l' (_, l) ~init = List.fold_right2 f l' l init

  (** Return the set of all identifiers bound in a given named-context. *)
  let to_vars (_, l) =
    List.fold_left (fun accu decl -> Id.Set.add (Declaration.get_id decl) accu) Id.Set.empty l

  (** Map a given named-context to a list where each {e local definition} is mapped to [true]
      and each {e local assumption} is mapped to [false]. *)
  let to_tags (_, l) =
    let rec aux l = function
      | [] -> l
      | Declaration.LocalDef _ :: ctx -> aux (true::l) ctx
      | Declaration.LocalAssum _ :: ctx -> aux (false::l) ctx
    in aux [] l

  let drop_bodies l = map_decl_smart Declaration.drop_body l

  let chop n (n', l) =
    let l1, l2 = List.chop n l in
    (n, l1), (n' - n, l2)

  let chop_nhyps n_local_assum (n_total, l) =
    let open Declaration in
    let rec aux acc_size l' = function
      | (0, l) -> ((acc_size, List.rev l'), (n_total - acc_size, l))
      | (n, (LocalDef _ as h) :: l) -> aux (acc_size + 1) (h::l') (n, l)
      | (n, (LocalAssum _ as h) :: l) -> aux (acc_size + 1) (h::l') (n-1, l)
      | (_, []) -> CErrors.anomaly (Pp.str "chop_nhyps: not enough hypotheses.")
    in aux 0 [] (n_local_assum,l)

  let split_when f (n, l) =
    let rec aux n_before acc = function
    | [] -> ((n_before, List.rev acc), (0, []))
    | d :: rest as l ->
      if f d then ((n_before, List.rev acc), (n - n_before, l))
      else aux (n_before + 1) (d :: acc) rest
    in aux 0 [] l

  (** [to_instance Ω] builds an instance [args] in reverse order such
      that [Ω ⊢ args:Ω] where [Ω] is a named context and with the local
      definitions of [Ω] skipped. Example: for [id1:T,id2:=c,id3:U], it
      gives [Var id1, Var id3]. All [idj] are supposed distinct. *)
  let to_instance mk (_, l) =
    let filter = function
      | Declaration.LocalAssum (id, _) -> Some (mk id.binder_name)
      | _ -> None
    in
    List.map_filter filter l

  (** [instance Ω] builds an instance [args] such
      that [Ω ⊢ args:Ω] where [Ω] is a named context and with the local
      definitions of [Ω] skipped. Example: for [id1:T,id2:=c,id3:U], it
      gives [Var id1, Var id3]. All [idj] are supposed distinct. *)
  let instance_list mk (_, l) =
    let filter = function
      | Declaration.LocalAssum (id, _) -> Some (mk id.binder_name)
      | _ -> None
    in
    List.rev (List.map_filter filter l)

  let instance mk l =
    Array.of_list (instance_list mk l)
end

module Compacted =
  struct
    module Declaration =
      struct
        type ('constr, 'types, 'r) pt =
          | LocalAssum of (Id.t,'r) pbinder_annot list * 'types
          | LocalDef of (Id.t,'r) pbinder_annot list * 'constr * 'types

        let map_constr f = function
          | LocalAssum (ids, ty) as decl ->
             let ty' = f ty in
             if ty == ty' then decl else LocalAssum (ids, ty')
          | LocalDef (ids, c, ty) as decl ->
             let ty' = f ty in
             let c' = f c in
             if c == c' && ty == ty' then decl else LocalDef (ids,c',ty')

        let of_named_decl = function
          | Named.Declaration.LocalAssum (id,t) ->
              LocalAssum ([id],t)
          | Named.Declaration.LocalDef (id,v,t) ->
              LocalDef ([id],v,t)
      end

    type ('constr, 'types, 'r) pt = ('constr, 'types, 'r) Declaration.pt list

    let fold f l ~init = List.fold_right f l init
  end
