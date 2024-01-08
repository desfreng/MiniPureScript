open CommonSymplify
open OperationSymplify

(* Le code du module AVL suivant est issu du livre :
       ``Apprendre à programmer avec OCaml''
   de Sylvain Conchon et Jean-Christophe Filliâtre. *)

module AVL (Ord : Set.OrderedType) : sig
  type key = Ord.t

  type t = private Empty | Node of t * key * t * int

  val add : key -> t -> t

  val empty : t
end = struct
  (***********************************************************************)
  (*                                                                     *)
  (*  OCaml library from the book ``Apprendre à programmer avec OCaml''  *)
  (*                                                                     *)
  (*  Sylvain Conchon and Jean-Christophe Filliâtre                      *)
  (*  Université Paris Sud                                               *)
  (*                                                                     *)
  (*  Copyright 2014 Université Paris Sud.  All rights reserved. This    *)
  (*  file is distributed under the terms of the GNU Library General     *)
  (*  Public License, with the same special exception on linking as the  *)
  (*  OCaml library. See http://caml.inria.fr/ocaml/license.fr.html      *)
  (*                                                                     *)
  (***********************************************************************)

  type key = Ord.t

  type t = Empty | Node of t * key * t * int

  let height = function Empty -> 0 | Node (_, _, _, h) -> h

  let node l v r = Node (l, v, r, 1 + max (height l) (height r))

  let balance l v r =
    let hl = height l in
    let hr = height r in
    if hl > hr + 1 then
      match l with
      | Node (ll, lv, lr, _) when height ll >= height lr ->
          node ll lv (node lr v r)
      | Node (ll, lv, Node (lrl, lrv, lrr, _), _) ->
          node (node ll lv lrl) lrv (node lrr v r)
      | _ ->
          assert false
    else if hr > hl + 1 then
      match r with
      | Node (rl, rv, rr, _) when height rr >= height rl ->
          node (node l v rl) rv rr
      | Node (Node (rll, rlv, rlr, _), rv, rr, _) ->
          node (node l v rll) rlv (node rlr rv rr)
      | _ ->
          assert false
    else node l v r

  let empty = Empty

  let rec add x = function
    | Empty ->
        Node (Empty, x, Empty, 1)
    | Node (l, v, r, _) as t ->
        let c = Ord.compare x v in
        if c = 0 then t
        else if c < 0 then balance (add x l) v r
        else balance l v (add x r)
end

module StringAVL = AVL (String)
module IntAVL = AVL (Int)

let mk_string_case typ var var_typ branches other =
  match var with
  | Either.Left v ->
      let avl =
        SMap.fold (fun s _ avl -> StringAVL.add s avl) branches StringAVL.empty
      in
      let rec build = function
        | StringAVL.Empty ->
            other
        | Node (Empty, s, Empty, _) ->
            (* This is compiled as a if :
               if v = s then branches[s] else other *)
            let cond =
              mk_eq bool_t
                (mk_sexpr var_typ (SVariable v))
                (mk_const string_t (String s))
            in
            let s_act = SMap.find s branches in
            mk_if typ cond s_act other
        | Node (l, s, r, _) ->
            (* This is compiled with a CompareAndBranch construction. *)
            let lower = build l in
            let equal = SMap.find s branches in
            let greater = build r in
            mk_sexpr typ
              (SCompareAndBranch {lhs= v; rhs= String s; lower; equal; greater})
      in
      build avl
  | Either.Right (Constant.String cst) -> (
    match SMap.find_opt cst branches with Some e -> e | None -> other )
  | _ ->
      (* A StringCase with not a string or a variable is not well typed *)
      assert false

let mk_int_case typ var var_typ branches other =
  match var with
  | Either.Left v ->
      let avl =
        IMap.fold (fun s _ avl -> IntAVL.add s avl) branches IntAVL.empty
      in
      let rec build = function
        | IntAVL.Empty ->
            other
        | Node (Empty, s, Empty, _) ->
            (* This is compiled as a if :
               if v = s then branches[s] else other *)
            let cond =
              mk_eq bool_t
                (mk_sexpr var_typ (SVariable v))
                (mk_const string_t (Int s))
            in
            let s_act = IMap.find s branches in
            mk_if typ cond s_act other
        | Node (l, s, r, _) ->
            (* This is compiled with a CompareAndBranch construction. *)
            let lower = build l in
            let equal = IMap.find s branches in
            let greater = build r in
            mk_sexpr typ
              (SCompareAndBranch {lhs= v; rhs= Int s; lower; equal; greater})
      in
      build avl
  | Either.Right (Constant.Int cst) -> (
    match IMap.find_opt cst branches with Some e -> e | None -> other )
  | _ ->
      (* An IntCase with not a string or a variable is not well typed *)
      assert false
