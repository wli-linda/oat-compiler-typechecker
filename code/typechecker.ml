open Ast
open Astlib
open Tctxt

(* Error Reporting ---------------------------------------------------------- *)
(* NOTE: Use type_error to report error messages for ill-typed programs. *)

exception TypeError of string

let type_error (l : 'a node) err = 
  let (_, (s, e), _) = l.loc in
  raise (TypeError (Printf.sprintf "[%d, %d] %s" s e err))


(* initial context: G0 ------------------------------------------------------ *)
(* The Oat types of the Oat built-in functions *)
let builtins =
  [ "array_of_string",  ([TRef RString],  RetVal (TRef(RArray TInt)))
  ; "string_of_array",  ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", ([TRef RString],  RetVal TInt)
  ; "string_of_int",    ([TInt], RetVal (TRef RString))
  ; "string_cat",       ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     ([TRef RString],  RetVoid)
  ; "print_int",        ([TInt], RetVoid)
  ; "print_bool",       ([TBool], RetVoid)
  ]

(* binary operation types --------------------------------------------------- *)
let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)
  | Eq | Neq -> failwith "typ_of_binop called on polymorphic == or !="

(* unary operation types ---------------------------------------------------- *)
let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

(* subtyping ---------------------------------------------------------------- *)
(* Decides whether H |- t1 <: t2 
    - assumes that H contains the declarations of all the possible struct types

    - you will want to introduce addition (possibly mutually recursive) 
      helper functions to implement the different judgments of the subtyping
      relation. We have included a template for subtype_ref to get you started.
      (Don't forget about OCaml's 'and' keyword.)
*)
let rec subtype (c : Tctxt.t) (t1 : Ast.ty) (t2 : Ast.ty) : bool =
  match t1 with
  | TBool -> t2 = TBool
  | TInt -> t2 = TInt
  | TRef rty1 -> begin
      match t2 with
      | TBool | TInt -> false
      | TRef rty2 | TNullRef rty2 -> subtype_ref c rty1 rty2
    end
  | TNullRef rty1 -> begin
      match t2 with
      | TBool | TInt | TRef _ -> false
      | TNullRef rty2 -> subtype_ref c rty1 rty2
    end

(* Decides whether H |-r ref1 <: ref2 *)
and subtype_ref (c : Tctxt.t) (t1 : Ast.rty) (t2 : Ast.rty) : bool =
  match t1 with
  | RString -> t2 = RString
  | RArray t1' -> begin match t2 with
      | RArray t2' -> t1' = t2' (* is this needed? *)
      | _ -> false
    end
  | RStruct id1 -> begin match t2 with
      (* not 100% sure of this *)
      | RStruct id2 -> lookup_struct_option id1 c != None &&
                       lookup_struct_option id2 c != None
      | _ -> false
    end
  | RFun (ls1, ret_ty1) ->
    let rec subtype_args_ls ls1 ls2 =
      match ls1, ls2 with
      | [], [] -> true
      | t1' :: tl1, t2' :: tl2 ->
        subtype c t2' t1' && subtype_args_ls tl1 tl2
      | _ -> false
    in
    begin match t2 with
      | RFun (ls2, ret_ty2) ->
        subtype_rt c ret_ty1 ret_ty2 && subtype_args_ls ls1 ls2
      | _ -> false
    end

and subtype_rt (c : Tctxt.t) (t1 : Ast.ret_ty) (t2 : Ast.ret_ty) : bool =
  match t1 with
  | RetVoid -> t2 = RetVoid
  | RetVal t1' -> begin match t2 with
      | RetVal t2' -> subtype c t1' t2'
      | _ -> false
    end

(* well-formed types -------------------------------------------------------- *)
(* Implement a (set of) functions that check that types are well formed according
   to the H |- t and related inference rules. Intuitively, this check can fail if an undefined reference appears as a component of `t`.

    - the function should succeed by returning () if the type is well-formed
      according to the rules

    - l is just an ast node that provides source location information for
      generating error messages (it's only needed for the type_error generation)

    - the function should fail using the "type_error" helper function if the 
      type is not well formed. Use `l` to indicate the location in the error.

    - tc contains the structure definition context
 *)
let rec typecheck_ty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.ty) : unit =
  match t with
  | TInt | TBool -> ()
  | TRef rty | TNullRef rty -> typecheck_ref l tc rty

and typecheck_ref (l : 'a Ast.node) (tc : Tctxt.t) (rty : Ast.rty) : unit = 
  match rty with
  | RString -> ()
  | RArray t -> typecheck_ty l tc t
  | RStruct id -> begin
      if lookup_struct_option id tc != None
      then ()
      else type_error l ("typecheck_ref: struct " ^ id ^ " not in ctxt?")
    end
  | RFun (ls, rt) ->
    let rec typecheck_args_ls args = 
      match ls with
      | [] -> ()
      | t' :: tl ->
        typecheck_ty l tc t';
        (* Why does this line throw me in an infinite loop? *)
        (*typecheck_args_ls tl*)
    in
    typecheck_args_ls ls;
    typecheck_rt l tc rt

and typecheck_rt (l : 'a Ast.node) (tc : Tctxt.t) (rt : Ast.ret_ty) : unit =
  match rt with
  | RetVoid -> ()
  | RetVal t -> typecheck_ty l tc t


(* A helper function to determine whether a type allows the null value *)
let is_nullable_ty (t : Ast.ty) : bool =
  match t with
  | TNullRef _ -> true
  | _ -> false

(* typechecking expressions ------------------------------------------------- *)
(* Typechecks an expression in the typing context c, returns the type of the
   expression.  This function should implement the inference rules given in the
   oat.pdf specification.  There, they are written:

       H; G; L |- exp : t

   See tctxt.ml for the implementation of the context c, which represents the
   four typing contexts: H - for structure definitions G - for global
   identifiers L - for local identifiers

   Returns the (most precise) type for the expression, if it is type correct
   according to the inference rules.

   Uses the type_error function to indicate a (useful!) error message if the
   expression is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   Notes: - Structure values permit the programmer to write the fields in any
   order (compared with the structure definition).  This means that, given the
   declaration struct T { a:int; b:int; c:int } The expression new T {b=3; c=4;
   a=1} is well typed.  (You should sort the fields to compare them.)

*)
let rec typecheck_exp (c : Tctxt.t) (e : Ast.exp node) : Ast.ty =
  match e.elt with
  | CNull rty -> TRef rty
  | CBool b -> TBool
  | CInt i -> TInt
  (*| CStr s -> TString*)
  | Id id -> begin match lookup_option id c with
      | Some x -> x
      | None -> type_error e ("typecheck_exp: id " ^ id ^ " not in ctxt")
    end
    
  | _ ->
    failwith "todo: implement typecheck_exp"

(* statements --------------------------------------------------------------- *)

(* Typecheck a statement 
   This function should implement the statment typechecking rules from oat.pdf.  

   Inputs:
    - tc: the type context
    - s: the statement node
    - to_ret: the desired return type (from the function declaration)

   Returns:
     - the new type context (which includes newly declared variables in scope
       after this statement)

     - A boolean indicating the return behavior of a statement:
        false:  might not return
        true:   definitely returns 

        in the branching statements, the return behavior of the branching 
        statement is the conjunction of the return behavior of the two 
        branches: both both branches must definitely return in order for 
        the whole statement to definitely return.

        Intuitively: if one of the two branches of a conditional does not 
        contain a return statement, then the entire conditional statement might 
        not return.
  
        looping constructs never definitely return 

   Uses the type_error function to indicate a (useful!) error message if the
   statement is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   - You will probably find it convenient to add a helper function that implements the 
     block typecheck rules.
*)
let rec typecheck_stmt (tc : Tctxt.t) (s:Ast.stmt node) (to_ret:ret_ty) : Tctxt.t * bool =
  match s.elt with
  | Assn (e1, e2) ->
    let t1 = typecheck_exp tc e1 in
    let t2 = typecheck_exp tc e2 in
    if subtype tc t2 t1
    then (tc, false)
    else type_error s ("exp not subtype of lhs in typecheck_stmt Assn")

  | _ -> failwith "todo: implement typecheck_stmt"

let rec typecheck_block (tc : Tctxt.t) (ls:Ast.block) (to_ret:ret_ty) : unit =
  match ls with
  | [] -> ()
  | stmt :: [] -> let _, bool = typecheck_stmt tc stmt to_ret in
    if not bool then type_error stmt "typecheck_block: last stmt doesn't return"
  | stmt :: tl -> let _, bool = typecheck_stmt tc stmt to_ret in
    if bool then type_error stmt "typecheck_block: non-last stmt def returns"
    else typecheck_block tc tl to_ret


(* struct type declarations ------------------------------------------------- *)
(* Here is an example of how to implement the TYP_TDECLOK rule, which is 
   is needed elswhere in the type system.
 *)

(* Helper function to look for duplicate field names *)
let rec check_dups fs =
  match fs with
  | [] -> false
  | h :: t -> (List.exists (fun x -> x.fieldName = h.fieldName) t) || check_dups t

let typecheck_tdecl (tc : Tctxt.t) id fs  (l : 'a Ast.node) : unit =
  if check_dups fs
  then type_error l ("Repeated fields in " ^ id) 
  else List.iter (fun f -> typecheck_ty l tc f.ftyp) fs

(* function declarations ---------------------------------------------------- *)
(* typecheck a function declaration 
    - extends the local context with the types of the formal parameters to the 
      function
    - typechecks the body of the function (passing in the expected return type
    - checks that the function actually returns
*)
let typecheck_fdecl (tc : Tctxt.t) (f : Ast.fdecl) (l : 'a Ast.node) : unit =
  let {frtyp; fname; args; body} = f in
  (* Do we need to check that arg ids are distinct? 
   * let fs = List.map (fun (ty, id) -> id) args in *)
  let rec extend_local_ctxt ls c =
    match ls with
    | [] -> c
    | (ty, id) :: tl ->
      let new_c = add_local c id ty in
      extend_local_ctxt tl new_c
  in
  let new_c = extend_local_ctxt args tc in
  typecheck_block new_c body frtyp
    
(* creating the typchecking context ----------------------------------------- *)

(* The following functions correspond to the
   judgments that create the global typechecking context.

   create_struct_ctxt: - adds all the struct types to the struct 'S'
   context (checking to see that there are no duplicate fields

     H |-s prog ==> H'


   create_function_ctxt: - adds the the function identifiers and their
   types to the 'G' context (ensuring that there are no redeclared
   function identifiers)

     H ; G1 |-f prog ==> G2


   create_global_ctxt: - typechecks the global initializers and adds
   their identifiers to the 'G' global context

     H ; G1 |-g prog ==> G2    


   NOTE: global initializers may mention function identifiers as
   constants, but can mention only other global values that were declared earlier
*)

let create_struct_ctxt (p:Ast.prog) : Tctxt.t =
  let tc = Tctxt.empty in
  let rec get_struct_ctxt prog c =
    match prog with
    | [] -> c
    | decl :: tl -> begin match decl with
        | Gtdecl tdecl ->
          let (id, fs) = tdecl.elt in
          typecheck_tdecl c id fs tdecl; (* shouldn't this be covered by typecheck_prog? *)
          let new_c = add_struct c id fs in
          get_struct_ctxt tl new_c
        | _ -> get_struct_ctxt tl c
      end
  in get_struct_ctxt p tc

let create_function_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  let structs = tc.structs in
  let rec get_function_ctxt prog c =
    match prog with
    | [] -> c
    | decl :: tl -> begin match decl with
        | Gfdecl fdecl ->
          let {frtyp; fname; args; _} = fdecl.elt in
          let rec get_args_ty ls a =
            match ls with
            | [] -> a
            | (t', id) :: tl -> get_args_ty tl (t' :: a)
          in
          (* Dunno if this is right, actually... *)
          let fun_ty = TRef (RFun (List.rev @@ get_args_ty args [], frtyp)) in
          let new_c = add_global c fname fun_ty in
          get_function_ctxt tl new_c
          (* typecheck_fdecl? *)
        | _ -> get_function_ctxt tl c
      end
  in get_function_ctxt p tc

let create_global_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  let rec get_global_ctxt prog c =
    match prog with
    | [] -> c
    | decl :: tl -> begin match decl with
        | Gvdecl gdecl ->
          let {name; init} = gdecl.elt in
          let ty = typecheck_exp c init in
          let new_c = add_global c name ty in
          get_global_ctxt tl new_c
        | _ -> get_global_ctxt tl c
      end
  in get_global_ctxt p tc


(* This function implements the |- prog and the H ; G |- prog 
   rules of the oat.pdf specification.   
*)
let typecheck_program (p:Ast.prog) : unit =
  let sc = create_struct_ctxt p in
  let fc = create_function_ctxt sc p in
  let tc = create_global_ctxt fc p in
  List.iter (fun p ->
    match p with
    | Gfdecl ({elt=f} as l) -> typecheck_fdecl tc f l
    | Gtdecl ({elt=(id, fs)} as l) -> typecheck_tdecl tc id fs l 
    | _ -> ()) p
