(** Id of a type variable that can be unified. *)
module TypeVar : sig
  type t

  val fresh : unit -> t
  (** [fresh ()] creates a new, unique type variable. *)

  module Map : Map.S with type key = t

  module Set : Set.S with type elt = t

  type 'a map = 'a Map.t

  type set = Set.t
end

(** Id of a universally quantified type variable. *)
module QTypeVar : sig
  type t

  val fresh : unit -> t
  (** [fresh ()] creates a new, unique quantified variable. *)

  module Map : Map.S with type key = t

  module Set : Set.S with type elt = t

  type 'a map = 'a Map.t

  type set = Set.t
end

(** Id of a type symbol *)
module Symbol : sig
  type t

  val fresh : string -> t
  (** [fresh n] creates a new symbol id, and bind it to [n]. [n] must be unique. *)

  val name : t -> string
  (** [name t] returns the name bind to [t]. *)

  val exists : string -> t option
  (** [exists n] checks if a symbol with name [n] exists. If so, return it.*)

  val pp : Format.formatter -> t -> unit
  (** Used to display a symbol *)

  module Map : Map.S with type key = t

  module Set : Set.S with type elt = t

  type 'a map = 'a Map.t

  type set = Set.t
end

(** Id of a variable *)
module Variable : sig
  type t

  val fresh : string -> t
  (** [fresh n] creates a new symbol id, and bind it to [n]. *)

  val name : t -> string
  (** [name t] returns the name bound to [t]. *)

  val pp : Format.formatter -> t -> unit
  (** Used to display a symbol *)

  module Map : Map.S with type key = t

  module Set : Set.S with type elt = t

  type 'a map = 'a Map.t

  type set = Set.t
end

(** Id of a constructor, linked to symbol *)
module Constructor : sig
  type t

  val fresh : string -> Symbol.t -> t
  (** [fresh n s] declares the new constructor [n] in the symbol [s].
      The constructor name [n] must be unique. *)

  val name : t -> string
  (** [name t] returns the name of the constructor. *)

  val symbol : t -> Symbol.t
  (** [symbol c] returns the symbol associed to the constructor [c] *)

  val exists : string -> (t * Symbol.t) option
  (** [exists n] checks if a constructor with name [n] exists. If so, return
      it with its symbol.*)

  val index_in_symbol : t -> int
  (** [index_in_symbol t] returns the index of this constructor in its symbol. *)

  val pp : Format.formatter -> t -> unit
  (** Used to display a symbol *)

  module Map : Map.S with type key = t

  module Set : Set.S with type elt = t

  type 'a map = 'a Map.t

  type set = Set.t
end

(** Id of a type symbol *)
module TypeClass : sig
  type t

  val fresh : string -> t
  (** [fresh n] creates a new symbol id, and bind it to [n]. [n] must be unique. *)

  val name : t -> string
  (** [name t] returns the name bind to [t]. *)

  val exists : string -> t option
  (** [exists n] checks if a symbol with name [n] exists. If so, return it.*)

  val pp : Format.formatter -> t -> unit
  (** Used to display a symbol *)

  module Map : Map.S with type key = t

  module Set : Set.S with type elt = t

  type 'a map = 'a Map.t

  type set = Set.t
end

(** Id of a function *)
module Function : sig
  type t

  val fresh : string -> TypeClass.t option -> t
  (** [fresh n] creates a new function with name [n]. *)

  val exists : string -> t option
  (** [exists n] checks if a symbol with name [n] exists. If so, return it.*)

  val name : t -> string
  (** [name t] returns the name bind to [t]. *)

  val type_class : t -> TypeClass.t option
  (** [type_class t] returns the potential type class associed to this function. *)

  val index_in_class : t -> int option
  (** [index_in_class t] returns the index of this function in its potential class. *)

  val pp : Format.formatter -> t -> unit
  (** Used to display a symbol *)

  module Map : Map.S with type key = t

  module Set : Set.S with type elt = t

  type 'a map = 'a Map.t

  type set = Set.t
end

(** Id of a global schema (or instance if this schema has no dependencies) *)
module Schema : sig
  type t

  val fresh : TypeClass.t -> t

  val typeclass : t -> TypeClass.t

  val pp : Format.formatter -> t -> unit

  val unique_int : t -> int

  module Map : Map.S with type key = t

  module Set : Set.S with type elt = t

  type 'a map = 'a Map.t

  type set = Set.t
end

(** Id of a local type-class instance *)
module Instance : sig
  type t

  val fresh : TypeClass.t -> t

  val typeclass : t -> TypeClass.t

  val pp : Format.formatter -> t -> unit

  module Map : Map.S with type key = t

  module Set : Set.S with type elt = t

  type 'a map = 'a Map.t

  type set = Set.t
end
