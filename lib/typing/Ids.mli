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

(** Id of a schema *)
module Schema : sig
  type t

  val fresh : unit -> t
  (** [fresh n] creates a new schema id, and bind it to [n]. [n] must be unique. *)

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

  val fresh : string -> t
  (** [fresh n] creates a new function with name [n]. *)

  val exists : string -> t option
  (** [exists n] checks if a symbol with name [n] exists. If so, return it.*)

  val name : t -> string
  (** [name t] returns the name bind to [t]. *)

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
