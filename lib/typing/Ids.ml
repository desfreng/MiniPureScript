(* We use functor when multiple module are implemented in the same way because
   we do not want any sharing between them (the hashtable MUST be discinct). *)

module SMap = Map.Make (String)
module SSet = Set.Make (String)
module IMap = Map.Make (Int)
module ISet = Set.Make (Int)

module UniqueId (M : sig end) = struct
  type t = int

  let fresh =
    let cpt = ref 0 in
    fun () ->
      incr cpt ;
      let id = !cpt in
      id

  module Map = IMap
  module Set = ISet

  type 'a map = 'a Map.t

  type set = Set.t
end

module TypeVar = UniqueId (struct end)

module QTypeVar = UniqueId (struct end)

module Symbol = struct
  type t = string

  let nb_constr_mapping = Hashtbl.create 17

  let fresh symb =
    if Hashtbl.mem nb_constr_mapping symb then
      raise (Invalid_argument ("The symbol '" ^ symb ^ "' is already defined."))
    else Hashtbl.add nb_constr_mapping symb 0 ;
    symb

  let exists symb =
    if Hashtbl.mem nb_constr_mapping symb then Some symb else None

  let name = Fun.id

  let pp ppf t = Format.pp_print_string ppf t

  module Map = SMap
  module Set = SSet

  type 'a map = 'a Map.t

  type set = Set.t
end

module TypeClass = struct
  type t = string

  let nb_fun_mapping = Hashtbl.create 17

  let fresh tcname =
    if Hashtbl.mem nb_fun_mapping tcname then
      raise
        (Invalid_argument ("The type class '" ^ tcname ^ "' is already defined.")
        )
    else Hashtbl.add nb_fun_mapping tcname 0 ;
    tcname

  let exists tcname =
    if Hashtbl.mem nb_fun_mapping tcname then Some tcname else None

  let name = Fun.id

  let pp ppf t = Format.pp_print_string ppf t

  module Map = Map.Make (String)
  module Set = Set.Make (String)

  type 'a map = 'a Map.t

  type set = Set.t
end

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

  let name id =
    let s = Hashtbl.find unique_int_to_name id in
    if s = "" then "var_" ^ string_of_int id else s

  let pp ppf t = Format.pp_print_string ppf (name t)

  module Map = Map.Make (Int)
  module Set = Set.Make (Int)

  type 'a map = 'a Map.t

  type set = Set.t
end

module Constructor = struct
  type t = string

  let cstr_infos = Hashtbl.create 17

  let fresh cstr symb =
    if Hashtbl.mem cstr_infos cstr then
      raise (Invalid_argument ("The symbol '" ^ cstr ^ "' is already defined."))
    else
      let cstr_id_in_symb = Hashtbl.find Symbol.nb_constr_mapping symb in
      Hashtbl.replace Symbol.nb_constr_mapping symb (cstr_id_in_symb + 1) ;
      Hashtbl.add cstr_infos cstr (symb, cstr_id_in_symb) ;
      cstr

  let name = Fun.id

  let symbol cstr = Hashtbl.find cstr_infos cstr |> fst

  let index_in_symbol cstr = Hashtbl.find cstr_infos cstr |> snd

  let exists cstr =
    match Hashtbl.find_opt cstr_infos cstr with
    | Some (sid, _) ->
        Some (cstr, sid)
    | None ->
        None

  let pp ppf t = Format.pp_print_string ppf t

  module Map = SMap
  module Set = SSet

  type 'a map = 'a Map.t

  type set = Set.t
end

module Function = struct
  type t = string

  let fun_infos = Hashtbl.create 17

  let fresh fname type_class =
    if Hashtbl.mem fun_infos fname then
      raise
        (Invalid_argument ("The function '" ^ fname ^ "' is already defined."))
    else
      match type_class with
      | Some cid ->
          let fun_id_in_tc = Hashtbl.find TypeClass.nb_fun_mapping cid in
          Hashtbl.replace TypeClass.nb_fun_mapping cid (fun_id_in_tc + 1) ;
          Hashtbl.add fun_infos fname (type_class, Some fun_id_in_tc) ;
          fname
      | None ->
          Hashtbl.add fun_infos fname (type_class, None) ;
          fname

  let name = Fun.id

  let type_class fname = Hashtbl.find fun_infos fname |> fst

  let index_in_class fname = Hashtbl.find fun_infos fname |> snd

  let exists fname =
    match Hashtbl.find_opt fun_infos fname with
    | Some _ ->
        Some fname
    | None ->
        None

  let pp ppf t = Format.pp_print_string ppf t

  module Map = SMap
  module Set = SSet

  type 'a map = 'a Map.t

  type set = Set.t
end

module TypeClassBindedId (_ : sig end) = struct
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

  module Map = IMap
  module Set = ISet

  type 'a map = 'a Map.t

  type set = Set.t
end

module Schema = TypeClassBindedId (struct end)

module Instance = TypeClassBindedId (struct end)
