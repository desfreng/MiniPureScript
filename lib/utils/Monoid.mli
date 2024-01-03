type 'a t

val empty : 'a t
(** The empty monoid. *)

val of_list : 'a list -> 'a t
(** Build a monoid from of list. *)

val of_elm : 'a -> 'a t
(** Build a monoid from of list. *)

val is_empty : 'a t -> bool
(** Checks if the monoid is empty *)

val ( <> ) : 'a t -> 'a t -> 'a t
(** Concatenate two monoid . *)

val fold_left : ('acc -> 'a -> 'acc) -> 'acc -> 'a t -> 'acc
(** [fold_left f init {b1; ...; bn}] is [{f (... (f (f init b1) b2) ...) bn}]. *)

val fold_right : ('a -> 'acc -> 'acc) -> 'a t -> 'acc -> 'acc
(** [fold_right f {a1; ...; an} init] is [{f a1 (f a2 (... (f an init) ...))}]. *)

val map : ('a -> 'b t) -> 'a t -> 'b t
(** [map f {a1; ...; an}] applies function [f] to the monoid [{a1, ..., an}],
   and builds the monoid [{f a1; ...; f an}] with the results returned by [f]. *)

val mapi : (int -> 'a -> 'b t) -> 'a t -> 'b t
(** Same as [map], but the function is applied to the index of
   the element as first argument (counting from 0), and the element
   itself as second argument. *)

val iter : ('a -> unit) -> 'a t -> unit
(** [iter f {a1; ...; an}] applies function [f] in turn to the monoid
   [{a1; ...; an}]. It is equivalent to [begin f a1; f a2; ...; f an; () end]. *)

val iteri : (int -> 'a -> unit) -> 'a t -> unit
(** Same as [iter], but the function is applied to the index of
   the element as first argument (counting from 0), and the element
   itself as second argument. *)

val to_list : 'a t -> 'a list
(** Convert a monoid to a list, concerve the order. *)

val first : 'a t -> 'a
(** Return the first element of the monoid.
   @raise Invalid_argument if the monoid is empty. *)
