(* We use functor when multiple module are implemented in the same way because
   we do not want any sharing between them (the hashtable MUST be discinct). *)

module UniqueId (M : sig end) = struct
  type t = int

  let fresh =
    let cpt = ref 0 in
    fun () ->
      incr cpt ;
      let id = !cpt in
      id

  module Map = Map.Make (Int)
  module Set = Set.Make (Int)

  type 'a map = 'a Map.t

  type set = Set.t
end

module TypeVar = UniqueId (struct end)

module QTypeVar = UniqueId (struct end)

module UniqueNamedId (M : sig end) = struct
  type t = string

  let name = Fun.id

  let pp ppf t = Format.pp_print_string ppf t

  module Map = Map.Make (String)
  module Set = Set.Make (String)

  type 'a map = 'a Map.t

  type set = Set.t

  let symbol_set = ref Set.empty

  let fresh symb =
    if Set.mem symb !symbol_set then
      raise (Invalid_argument ("The symbol '" ^ symb ^ "' is already defined."))
    else symbol_set := Set.add symb !symbol_set ;
    symb

  let exists name = if Set.mem name !symbol_set then Some name else None
end

module Symbol = UniqueNamedId (struct end)

module Function = UniqueNamedId (struct end)

module TypeClass = UniqueNamedId (struct end)

module Variable = struct
  type t = int

  let unique_int_to_name = Hashtbl.create 17

  let fresh =
    let cpt = ref 0 in
    fun name ->
      incr cpt ;
      let unique_int = !cpt in
      Hashtbl.add unique_int_to_name unique_int name ;
      unique_int

  let name id = Hashtbl.find unique_int_to_name id

  let pp ppf t = Format.pp_print_string ppf (name t)

  module Map = Map.Make (Int)
  module Set = Set.Make (Int)

  type 'a map = 'a Map.t

  type set = Set.t
end

module Constructor = struct
  type t = string

  let cstr_2_symb = Hashtbl.create 17

  let fresh cstr symb =
    if Hashtbl.mem cstr_2_symb cstr then
      raise (Invalid_argument ("The symbol '" ^ cstr ^ "' is already defined."))
    else Hashtbl.add cstr_2_symb cstr symb ;
    cstr

  let name = Fun.id

  let symbol cstr = Hashtbl.find cstr_2_symb cstr

  let exists cstr =
    match Hashtbl.find_opt cstr_2_symb cstr with
    | Some sid ->
        Some (cstr, sid)
    | None ->
        None

  let pp ppf t = Format.pp_print_string ppf t

  module Map = Map.Make (String)
  module Set = Set.Make (String)

  type 'a map = 'a Map.t

  type set = Set.t
end

module Schema = struct
  type t = int

  let schema_2_typeclass = Hashtbl.create 17

  let fresh =
    let cpt = ref 0 in
    fun tc ->
      incr cpt ;
      let id = !cpt in
      Hashtbl.add schema_2_typeclass id tc ;
      id

  let pp = Format.pp_print_int

  let typeclass t = Hashtbl.find schema_2_typeclass t

  module Map = Map.Make (Int)
  module Set = Set.Make (Int)

  type 'a map = 'a Map.t

  type set = Set.t
end
