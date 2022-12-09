
open Format
open Lib
open Ast
open Tast

let debug = ref false

let dummy_loc = Lexing.dummy_pos, Lexing.dummy_pos

exception Error of Ast.location * string
exception Anomaly of string


let error loc e = raise (Error (loc, e))




(* TODO environnement pour les types structure *)
let structure_table : (string, structure) Hashtbl.t = Hashtbl.create 10

(* TODO environnement pour les fonctions *)
let structure_fun : (string, function_) Hashtbl.t = Hashtbl.create 10



(* ptyp to typ *)
let rec type_type = function
  | PTident { id = "int" } -> Tint
  | PTident { id = "bool" } -> Tbool
  | PTident { id = "string" } -> Tstring
  | PTptr ty -> Tptr (type_type ty)
  | PTident id -> 
    begin try
      let s = Hashtbl.find structure_table id.id in
      Tstruct s
    with 
    |Not_found -> error id.loc (Printf.sprintf "declaration of variable %s unkown" id.id)
    end




let rec eq_type ty1 ty2 = match ty1, ty2 with
  | Tint, Tint | Tbool, Tbool | Tstring, Tstring -> true
  | Tstruct s1, Tstruct s2 -> s1 == s2
  | Tptr ty1, Tptr ty2 -> eq_type ty1 ty2
  | Tptr(Twild), _ | _, Tptr(Twild) -> true
  | Tmany(l1), Tmany(l2) -> 
    if List.compare_lengths l1 l2 <> 0 then false
    else if not(List.for_all2 eq_type l1 l2) then false
    else true
  | _ -> false
    (* TODO autres types *)





let fmt_used = ref false
let fmt_imported = ref false

let evar v = { expr_desc = TEident v; expr_typ = v.v_typ }

let new_var =
  let id = ref 0 in
  fun x loc ?(used=false) ty ->
    incr id;
    { v_name = x; v_id = !id; v_loc = loc; v_typ = ty; v_used = used; v_addr = 0; v_depth = 0 }

module Env = struct
  module M = Map.Make(String)
  type t = var M.t
  let empty = M.empty
  let find = M.find
  let add env v = M.add v.v_name v env

  let all_vars = ref []
  let check_unused () =
    let check v =
      if v.v_name <> "_" && v.v_used = false then error v.v_loc "unused variable" in
    List.iter check !all_vars


  let var x loc ?used ty env =
    let v = new_var x loc ?used ty in
    all_vars := v :: !all_vars;
    add env v, v

  (* TODO type () et vecteur de types *)
end



(* verifie si une expression est une l-value *)
let rec check_lvalue = function
  | TEident _ -> true
  | TEdot (e,x) when check_lvalue e.expr_desc -> true
  | TEunop (Ustar, e) when e.expr_desc <> TEnil -> true
  | _ -> false


(* renvoit une liste de variables avec les mêmes types que dans expr (les listes ont la même longueur)
   je l'utilise dans PEvars, est-ce-que je dois utiliser la fonction var ? *)
let make_vartyp params type_li =
  let make_thisvar i t = {v_name = i.id; v_loc = i.loc; v_typ = t; v_id=0; v_depth=0; v_used=false ;v_addr =0} in
  List.map2 make_thisvar params type_li


(* renvoit une liste de variables avec le type t *)
let make_vars params t =
  let make_thisvar i = {v_name = i.id; v_loc = i.loc; v_typ = t; v_id=0; v_depth=0; v_used=false ;v_addr =0} in
  List.map make_thisvar params





(* vérifie que le typage des variables d'une fonctions est correcte 
   càd si il y a un élément de type Tmany, c'est le seul *)
let check_variables loc l =
  let rec check_var_aux = function
    | [] -> ()
    | expression :: q -> 
      if q = [] then ();
      begin match expression.expr_typ with 
        | Tmany(_) -> error loc "wrong arguments applied to function";
        | _ -> check_var_aux q end
  in match l with
  | [] -> ()
  | expression :: q -> begin
    match expression.expr_typ with
    | Tmany(_) -> if q <> [] then error loc "wrong arguments applied to function"
    | _ -> check_var_aux q end
    



let tvoid = Tmany []
let make d ty = { expr_desc = d; expr_typ = ty }
let stmt d = make d tvoid

(* pexpr -> expr, bool *)
let rec expr env e =
 let e, ty, rt = expr_desc env e.pexpr_loc e.pexpr_desc in
  { expr_desc = e; expr_typ = ty }, rt


(* environnement, loc, pexpr_desc -> expr_desc, typ, bool *)
and expr_desc env loc = function

  | PEskip ->
    TEskip, tvoid, false

  | PEconstant c ->

    begin match c with
      | Cbool(_) -> TEconstant c, Tbool, false
      | Cint(_) -> TEconstant c, Tint, false
      | Cstring(_) -> TEconstant c, Tstring, false
      end

  | PEbinop (op, e1, e2) -> 

    let exp1, rt1 = expr env e1 in
    let exp2, rt2 = expr env e2 in
    let ty1 = exp1.expr_typ in
    let ty2 = exp2.expr_typ in
    begin match op with
    | Badd | Bsub | Bmul | Bdiv | Bmod
    -> if ty1 <> Tint then error e1.pexpr_loc "type int attendu pour cette opération" ;
      if ty2 <> Tint then error e2.pexpr_loc "type int attendu pour cette opération";
      TEbinop (op, exp1, exp2), Tint, false
    | Beq | Bne
    -> if ty1 <> ty2 then error e1.pexpr_loc "types incompatibles pour cette opération";
      TEbinop (op, exp1, exp2), Tbool, false
    
    | Blt | Ble | Bgt | Bge
    -> if ty1 <> Tint then error e1.pexpr_loc "type int attendu pour cette opération" ;
      if ty2 <> Tint then error e2.pexpr_loc "type int attendu pour cette opération";
      TEbinop (op, exp1, exp2), Tbool, false

    | Band | Bor
    -> if ty1 <> Tbool then error e1.pexpr_loc "type bool attendu pour cette opération" ;
    if ty2 <> Tbool then error e2.pexpr_loc "type bool attendu pour cette opération";
    TEbinop (op, exp1, exp2), Tbool, false
    end
  
  | PEunop (Uamp, e1) -> 

    let exp, rt = expr env e1 in
    Printf.printf "expression in amp evaluated";
    if not (check_lvalue exp.expr_desc) then error loc "& requires l-value";
    TEunop(Uamp, exp), Tptr(exp.expr_typ), false

  | PEunop (Uneg | Unot | Ustar as op, e1) ->
    
    let exp, rt = expr env e1 in
    let t = exp.expr_typ in
    if not (check_lvalue exp.expr_desc) then error loc "operation requires l-value";
    begin match op with
      | Uneg -> 
          if t <> Tint then error loc "minus needs type int";
          TEunop(op, exp), Tint, false
      | Unot ->
          if t <> Tbool then error loc "negation needs type bool";
          TEunop(op, exp), Tbool, false
      | Ustar -> begin match t with
          | Tptr(a) -> TEunop(op, exp), a, false
          | _ -> error loc "star needs a pointer" end
    end

  | PEcall ({id = "fmt.Print"; loc = loc}, el) ->

    if not !fmt_imported then error loc "fmt used but not imported";
    fmt_used := true;
    let find_expr e = (let a, b = expr env e in a) in
    let l = List.map find_expr el in
    check_variables loc l; (* si il ya un Tmany il doit être le seul *)
    TEprint l, tvoid, false

  | PEcall ({id="new"}, [{pexpr_desc=PEident {id}}]) ->

    let ty = match id with
      | "int" -> Tint | "bool" -> Tbool | "string" -> Tstring
      | _ ->
       if not(Hashtbl.mem structure_table id) then error loc ("no such type " ^ id)
       else type_type (PTident{ id; loc })
    in TEnew ty, Tptr ty, false

  | PEcall (id, el) ->

    begin try
    let f = Hashtbl.find structure_fun id.id in
    let dep_expr_desc e = (let (enew, rt) = expr env e in enew) in
    let l = List.map dep_expr_desc el in
    check_variables loc l; (* si il ya un Tmany il doit être le seul *)
    let vartype_list = List.map (fun v -> v.v_typ) f.fn_params in
    begin match (List.map (fun x -> x.expr_typ) l) with
      | [Tmany(li)] -> 
        Printf.printf "%s, %d, %d\n" id.id (List.length(vartype_list)) (List.length(li));
        if (List.length(vartype_list) <> List.length(li)) then error loc "1function called with the wrong number of parameters";
        if not(List.equal eq_type vartype_list li) then error loc "1function called with wrong type parameters"

      | a :: q ->
        Printf.printf "%s, %d, %d\n" id.id (List.length(vartype_list)) (List.length(el));
        if List.length(vartype_list) <> List.length(el) then error loc "2function called with the wrong number of parameters";
        if not(List.equal eq_type vartype_list (List.map (fun e -> e.expr_typ) l)) then error loc "2function called with wrong type parameters"
    end;
    let typ = match l with
      | [] -> tvoid
      | [e] -> e.expr_typ
      | e :: q -> Tmany(f.fn_typ)
    in TEcall(f, l), typ, false
    with Not_found -> error loc ( Printf.sprintf "Function %s not defined" id.id ) end

  | PEfor (e, b) ->
     
    let exp1, rt1 = expr env e in
    let exp2, rt2 = expr env b in
    let ty1 = exp1.expr_typ in
    let ty2 = exp2.expr_typ in
    if not(eq_type ty1 Tbool) then error e.pexpr_loc "Condition in for loop is not boolean";
    TEfor(exp1, exp2), ty2, rt2

  | PEif (e1, e2, e3) ->

    let exp1, rt1 = expr env e1 in
    let exp2, rt2 = expr env e2 in
    let exp3, rt3 = expr env e3 in
    let ty1 = exp1.expr_typ in
    let ty2 = exp2.expr_typ in
    let ty3 = exp3.expr_typ in
    if not(eq_type ty1 Tbool) then error e1.pexpr_loc "Condition in if clause is not boolean";
    if eq_type ty2 ty3 then error loc "Same type expected in if clause";
    TEif(exp1, exp2, exp3), ty2, (rt2 && rt3)

  | PEnil -> TEnil, Tptr(Twild), false 
    
  | PEident {id=id} ->

    (try let v = Env.find id env in begin Printf.printf "found variable\n";
      v.v_used <- true;
      TEident v, v.v_typ, false end
    with Not_found -> error loc ("unbound variable " ^ id))

  | PEdot (e, id) ->

    let expression, rt = expr env e in
    Printf.sprintf "dot done";
    let ty = expression.expr_typ in 
    begin match ty with
      | Tptr(Tstruct(stru))
      | Tstruct(stru) ->
        if not(Hashtbl.mem structure_table (stru.s_name)) then error e.pexpr_loc (Printf.sprintf "structure named %s is not defined" stru.s_name);
        begin try let fie = Hashtbl.find (stru.s_fields) id.id in
        TEdot(expression, fie), fie.f_typ, false
        with Not_found -> error loc (Printf.sprintf "field %s not defined" id.id) end
      | _ -> error (e.pexpr_loc) "expression is not type structure" end

  | PEassign (lvl, el) ->

    let dep_expr_desc e = (let (enew, rt) = expr env e in enew) in
    let elvl = List.map dep_expr_desc lvl in 
    if not( List.for_all check_lvalue (List.map (fun e -> e.expr_desc) elvl) ) then error loc "Can only assign l-values";
    let l = List.map dep_expr_desc el in
    check_variables loc l; (* si il ya un Tmany il doit être le seul *)
    begin match (List.map (fun x -> x.expr_typ) l) with
      | [Tmany(li)] -> 
        
        if (List.length(elvl) <> List.length(li)) then error loc "1assigned wrong number of l-values";
        if not(List.equal eq_type (List.map (fun e -> e.expr_typ) elvl) li) then error loc "1function called with wrong type parameters"

      | a :: q ->
        
        if List.length(elvl) <> List.length(l) then error loc "2assigned wrong number of l-values";
        if not(List.equal eq_type (List.map (fun e -> e.expr_typ) elvl) (List.map (fun e -> e.expr_typ) l)) then error loc "2function called with wrong type parameters"
    end;
    TEassign (elvl, l), tvoid, false 

  | PEreturn el ->

    let dep_expr_desc e = (let (enew, rt) = expr env e in enew) in
    let l = List.map dep_expr_desc el in
    check_variables loc l;
    TEreturn l, Tmany(List.map (fun e -> e.expr_typ) l), true

  | PEblock el -> (* parcourir el un à un, changer env si on rencontre un PEassign ou PEvars *)

    begin 
    let rec add_to_env environ vars = match vars with
      | [] -> environ
      | a :: q -> let (newenv, v) = (Env.var a.v_name a.v_loc a.v_typ environ) in add_to_env newenv q
    in let rec block_aux envi l ty_returned returnfound el = match el with

      | [] -> TEblock(l), ty_returned, returnfound

      | ({pexpr_desc = PEvars(x, _ ,li); pexpr_loc = loc} as a) :: q ->

        let exp, rt = expr envi a in
        let TEvars(vars, list) = exp.expr_desc in
        block_aux (add_to_env envi vars) (exp :: l) ty_returned returnfound q

      | a :: q -> 

        let exp, rt = expr envi a in
        let t = exp.expr_typ in
        if (rt = true && returnfound = false) then block_aux envi (exp :: l) t true q
        else if (returnfound = true && (not (eq_type ty_returned t))) then error a.pexpr_loc "function needs to return same types"
        else block_aux envi (exp :: l) ty_returned returnfound q

    in block_aux env [] tvoid false el
    end


  | PEincdec (e, op) ->

    let expression, rt = expr env e in
    if expression.expr_typ <> Tint then error loc "operation can only be used on integers";
    if not(check_lvalue expression.expr_desc) then error loc "operation can only be used on l-values";
    TEincdec(expression, op), Tint, false

  | PEvars (params, ty, el)  ->

    let dep_expr_desc e = (let (enew, rt) = expr env e in enew) in
    let l = List.map dep_expr_desc el in
    check_variables loc l;
    let compare_len li1 li2 =
      if (List.compare_lengths li1 li2) <> 0 then error loc "not assigning the right number of expressions to variables" in
    begin match (ty, l) with 
      | (Some typ, []) ->

        let t = type_type typ in
        let vars = make_vars params t in
        TEvars(vars, []), tvoid, false

      | (_, []) -> error loc "need expressions to assign"
      | (_, [e]) when e.expr_typ = Tmany([])  -> error loc "cannot assign type unit to variables"

      | (None, [{expr_desc; expr_typ = Tmany(li)}]) ->

        compare_len params li;
        let vars = make_vartyp params li in
        TEvars(vars, l), tvoid, false

      | (Some typ, [{expr_desc; expr_typ = Tmany(li)} as e]) -> 

        compare_len params li;
        let t = type_type typ in
        if List.exists (fun ty -> eq_type ty t) li then error loc "expressions need to be of given type";
        let vars = make_vars params t in
        TEvars(vars, [e]), tvoid, false

      | (None, l) ->

        compare_len params l;
        if List.exists (fun e -> e.expr_desc = TEnil) l then error loc "cannot assign type void to variables";
        let vars = make_vartyp params (List.map (fun e -> e.expr_typ) l) in
        TEvars(vars, l), tvoid, false

      | (Some typ, l) ->

        compare_len params l;
        let t = type_type typ in
        if List.exists (fun e -> eq_type e.expr_typ t) l then error loc "expressions need to be of given type";
        let vars = make_vars params t in
        TEvars(vars, l), tvoid, false
    end
    



let found_main = ref false




(* 1. declare structures *)
let phase1 = function
  | PDstruct { ps_name = { id = id; loc = loc }} -> 

    (* on vérifie que le nom de la structure n'est pas déjà dans structure_table et on sinon l'ajoute *)
    if Hashtbl.mem structure_table id then error loc (Printf.sprintf "structure %s already in environment" id);
    Hashtbl.add structure_table id {s_name = id; s_fields = Hashtbl.create 10; s_size = 0}

  | PDfunction _ -> ()



let rec sizeof = function
  | Tint | Tbool | Tstring | Tptr _ -> 8
  | Tmany l -> List.fold_left (fun i x -> i + sizeof x) 0 l
  | Tstruct s -> Hashtbl.fold (fun _ b c -> c + sizeof (b.f_typ)) s.s_fields 0



let checkmain f =
  if not(f.pf_params = [] && f.pf_typ = []) 
  then error f.pf_name.loc "Fonction main mal typée"
  else found_main := true


  let rec check_type = function
  | PTident { id = "int" }
  | PTident { id = "bool" }
  | PTident { id = "string" } -> ()
  | PTptr ty -> check_type ty
  | PTident id -> 
    try 
      Hashtbl.find structure_table id.id; ()
    with _ -> 
    error id.loc (Printf.sprintf "unknown type %s" id.id)


let check_typelist tyl = List.iter check_type tyl

let check_params h pl = 
  let rec aux_check = function 
    | [] -> ()
    | ({id = id; loc = loc}, t) :: q ->
        begin if Hashtbl.mem h id then error loc (Printf.sprintf "variable names %s already defined" id);
        check_type t;
        Hashtbl.add h id new_var;
        aux_check q end
  in aux_check pl

let make_fields h fl  =
  let size = ref 0 in
  let rec aux_fields = function
    | [] -> ()
    | ({id = id; loc = loc}, t) :: q ->
      begin if Hashtbl.mem h id then (error loc (Printf.sprintf "field %s already defined" id)) ;
      check_type t ;
      Hashtbl.add h id {f_name = id; f_typ = type_type t; f_ofs = 0} ;
      let s = type_type t in size := !size + (sizeof s) ;
      (aux_fields q) end
  in aux_fields fl;
  !size;;
      


(* 2. declare functions and type fields *)
let phase2 = function
  | PDfunction { pf_name={id; loc}; pf_params=pl; pf_typ=tyl; pf_body = b } ->

    (* cas particulier de id = main*)
    if id = "main" then checkmain { pf_name={id; loc}; pf_params=pl; pf_typ=tyl; pf_body = b } ;
    (* on vérifie que le nom de toutes les variables sont distinctes et que leurs types sont bien formés *)
    check_params (Hashtbl.create 10) pl;
    (* on vérifie que les types en sortie sont bien formés *)
    check_typelist tyl;
    (* on vérifie que le nom de la structure n'est pas déjà dans structure_table et on sinon l'ajoute *)
    if Hashtbl.mem structure_fun id then error loc(Printf.sprintf "function named %s already in environment" id);
    Hashtbl.add structure_fun id {fn_name = id; fn_params = []; fn_typ = []}

  | PDstruct { ps_name = {id}; ps_fields = fl } ->

    (* création d'une hashtable pour stocker les champs
       tout en vérifiant l'unicité des noms et que leur types sont bien formés
       et on somme la taille de tous les paramètres pour obtenir s_size *)
    let structure_fields : (string, field) Hashtbl.t = Hashtbl.create 10 in
    let size = make_fields structure_fields fl in
    (* on rajoute dans le contexte *)
    Hashtbl.replace structure_table id {s_name = id; s_fields = structure_fields ; s_size = size}




let rec paramli_to_varli names = function
  | [] -> ([], Env.empty)
  | ({loc = loc; id = id}, t) :: q -> begin
      if List.mem id names then (error loc (Printf.sprintf "variable %s already defined" id));
      let (varlist, env) = paramli_to_varli (id::names) q in
      let (nvenv, v) = Env.var id loc (type_type t) env in
      (v::varlist, nvenv)
      end

let rec check_recursive name = function
    | [] -> ()
    | ({loc = loc; id = id}, _ )  :: q->
        begin if name = id then error loc (Printf.sprintf "structure %s is defined recursively" id);
        check_recursive name q end



(* 3. type check function bodies *)
let decl = function
  | PDfunction { pf_name={id; loc}; pf_body = e; pf_typ=tyl; pf_params = pl } ->

    (* on construit fn_params (varli) ainsi que l'environnement (envi) *)
    begin let (varli, envi) = paramli_to_varli [] pl in
    Printf.printf "%s, %d \n" id (List.length(varli));
    (* on construit fn_type *)
    let typli = List.map type_type tyl in
    (* function créée *)
    let f = { fn_name = id; fn_params = varli; fn_typ = typli} in
    Hashtbl.replace structure_fun id f;
    (* on verifie qu'on type e dans envi
       on récupère l'expression et un booléen indiquant si elle possède un return *)
    let (expression, rt) = expr envi e in
    (* on vérifie que le return n'existe pas ssi expression est de type Tvoid on vérifie que le return renvoit bien ce qu'il faut *)
    begin match (rt, typli) with
      | (false, a::q) -> if (not(eq_type a tvoid) && q=[]) then error loc (Printf.sprintf "function %s has no return instruction" id)
      | (true, tvoid) -> error loc (Printf.sprintf "function %s shouldn't have a return instruction" id)
      | (true, [t] ) -> if not( eq_type expression.expr_typ t ) then error loc (Printf.sprintf "function %s does not return expected type" id)
      | (true, _) -> if not(eq_type (expression.expr_typ) (Tmany(typli))) then error loc (Printf.sprintf "function %s does not return expected type" id)
    end;
    TDfunction (f, expression)
    end

  | PDstruct {ps_name={id}; ps_fields = pl} ->

    (* check if structure is not recursive *)
    begin let s = Hashtbl.find structure_table id in
    check_recursive id pl;
    TDstruct s end 





let file ~debug:b (imp, dl) =
  debug := b;
  fmt_imported := imp;
  List.iter phase1 dl;
  List.iter phase2 dl;
  if not !found_main then error dummy_loc "missing method main";
  let dl = List.map decl dl in
  Env.check_unused (); 
  if imp && not !fmt_used then error dummy_loc "fmt imported but not used";
  dl
