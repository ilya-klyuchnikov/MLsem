module Variable = struct

  type kind = Let | Lambda | Gen
  let data : (int, string option * Position.t list * kind) Hashtbl.t = Hashtbl.create 100

  type t = int
  let compare = compare
  let equals a b = a = b

  let next_id =
    let last = ref 0 in
    fun () ->
      last := !last + 1 ;
      !last

  let create (k:kind) display_name =
    let id = next_id () in
    Hashtbl.add data id (display_name, [], k) ;
    id

  let create_let display_name =
    create Let display_name

  let create_lambda display_name =
    create Lambda display_name

  let create_gen display_name =
    create Gen display_name

  let attach_location id loc =
    let (name, locs, k) = Hashtbl.find data id in
    Hashtbl.replace data id (name, loc::locs, k)

  let get_locations id =
    let (_, locs, _) = Hashtbl.find data id
    in locs

  let is_let_var id =
    let (_, _, k) = Hashtbl.find data id in
    k = Let

  let is_lambda_var id =
    let (_, _, k) = Hashtbl.find data id in
    k = Lambda

  let get_name id =
    let (name, _, _) = Hashtbl.find data id in
    name

  let get_unique_name id =
    let prefix = match get_name id with None -> "" | Some str -> str in
    prefix^"_"^(string_of_int id)

  let pp fmt t =
    match get_name t with
    | None -> Format.fprintf fmt "%d" t
    | Some str -> Format.fprintf fmt "%s" str
    
  let show t =
    match get_name t with
    | None -> string_of_int t
    | Some str -> str
end

module VarMap = Map.Make(Variable)
module VarSet = Set.Make(Variable)