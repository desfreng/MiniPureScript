(** A small module to concatenate things quickly *)
type 'a t = Empty | Leaf of 'a | Concat of 'a t * 'a t

(** The empty set. *)
let empty = Empty

(** Build a monoid from an element. *)
let of_elm x = Leaf x

(** Concatenate two set. *)
let ( <> ) a b =
  match (a, b) with Empty, t | t, Empty -> t | a, b -> Concat (a, b)

(** Build a monoid from of list. *)
let of_list x = List.fold_left (fun acc elm -> acc <> of_elm elm) empty x

let rec fold_left f acc = function
  | Empty ->
      acc
  | Leaf x ->
      f acc x
  | Concat (left, right) ->
      let left_acc = fold_left f acc left in
      fold_left f left_acc right

let rec fold_right f m acc =
  match m with
  | Empty ->
      acc
  | Leaf x ->
      f x acc
  | Concat (left, right) ->
      let right_acc = fold_right f right acc in
      fold_right f left right_acc

let rec map f = function
  | Empty ->
      Empty
  | Leaf x ->
      f x
  | Concat (left, right) ->
      Concat (map f left, map f right)

let rec mapi index f m =
  match m with
  | Empty ->
      (Empty, index)
  | Leaf x ->
      ((f index) x, index + 1)
  | Concat (left, right) ->
      let left_part, index = mapi index f left in
      let right_part, index = mapi index f right in
      (Concat (left_part, right_part), index)

let mapi f m = fst (mapi 0 f m)

let iter f = fold_left (fun () -> f) ()

let iteri f m =
  let _ = fold_left (fun i x -> f i x ; i + 1) 0 m in
  ()

let to_list x = fold_left (fun acc x -> x :: acc) [] x |> List.rev

let is_empty = function Empty -> true | Leaf _ | Concat _ -> false

let rec first = function
  | Empty ->
      raise (Invalid_argument "empty monoid")
  | Leaf x ->
      x
  | Concat (l, _) ->
      first l
