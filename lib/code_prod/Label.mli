type label = string

module LabelMap : Map.S with type key = label

val pp : Format.formatter -> label -> unit

val local_lbl : Ids.Function.t -> label

val function_lbl : Ids.Function.t -> label option -> label

val schema_lbl : Ids.Schema.t -> label

val string_lbl : unit -> label

val code_lbl : unit -> label

val with_prefix : string -> label
