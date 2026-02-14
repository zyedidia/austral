(*
   LinIR backend for the Austral compiler.
*)
open Id
open Identifier
open Type
open EnvTypes
open Env
open MonoType
open Stages.Tast
open Stages.Mtast
open MtastUtil
open Escape
open Error
open Common

(* --- Name generation (reuse CodeGen's scheme) --- *)

let austral_prefix: string = ""

let gen_ident (i: identifier): string =
  austral_prefix ^ (ident_string i)

let gen_decl_id (id: decl_id): string =
  let (DeclId i) = id in
  austral_prefix ^ "decl_" ^ (string_of_int i)

let gen_mono_id (id: mono_id): string =
  let (MonoId i) = id in
  austral_prefix ^ "mono_" ^ (string_of_int i)

let gen_ins_meth_id (id: ins_meth_id): string =
  let (InsMethId i) = id in
  austral_prefix ^ "meth_" ^ (string_of_int i)

(* --- SSA codegen context --- *)

type val_id = int

let val_none: val_id = -1

type func_ctx = {
  mutable next_val: int;
  mutable next_block: int;
  mutable next_region: int;
  buf: Buffer.t;
  mutable completed_blocks: string list;  (* finished blocks, reversed *)
  mutable cur_label: string;
  mutable cur_params: string;
  mutable locals: (string * val_id) list;
  mutable local_types: (string * string) list;  (* variable name -> LinIR type string *)
  mutable data_segs: (string * string) list;
  mutable next_data: int;
  env: env;
}

let fresh_val (ctx: func_ctx): val_id =
  let v = ctx.next_val in
  ctx.next_val <- v + 1;
  v

let fresh_block (ctx: func_ctx): string =
  let n = ctx.next_block in
  ctx.next_block <- n + 1;
  "bb" ^ (string_of_int n)

let fresh_region (ctx: func_ctx): string =
  let n = ctx.next_region in
  ctx.next_region <- n + 1;
  "%R" ^ (string_of_int n)

let emit (ctx: func_ctx) (s: string): unit =
  Buffer.add_string ctx.buf ("    " ^ s ^ "\n")

let val_str (v: val_id): string =
  "%" ^ (string_of_int v)

let lookup_var (ctx: func_ctx) (name: string): val_id =
  match List.assoc_opt name ctx.locals with
  | Some v -> v
  | None -> internal_err ("LinIRGen: variable not found: " ^ name)

let bind_var (ctx: func_ctx) (name: string) (v: val_id): unit =
  (* Update or add binding *)
  ctx.locals <- (name, v) :: (List.remove_assoc name ctx.locals)

let bind_var_with_type (ctx: func_ctx) (name: string) (v: val_id) (ty: string): unit =
  bind_var ctx name v;
  ctx.local_types <- (name, ty) :: (List.remove_assoc name ctx.local_types)

let get_local_type (ctx: func_ctx) (name: string): string =
  match List.assoc_opt name ctx.local_types with
  | Some t -> t
  | None -> "unit"  (* fallback *)

let finish_block (ctx: func_ctx) (terminator: string): unit =
  Buffer.add_string ctx.buf ("    " ^ terminator ^ "\n");
  let block_text =
    "  " ^ ctx.cur_label ^ "(" ^ ctx.cur_params ^ "):\n"
    ^ (Buffer.contents ctx.buf)
  in
  ctx.completed_blocks <- block_text :: ctx.completed_blocks;
  Buffer.clear ctx.buf

let start_block (ctx: func_ctx) (label: string) (params: string): unit =
  ctx.cur_label <- label;
  ctx.cur_params <- params;
  Buffer.clear ctx.buf

(* --- Variable threading helpers for control flow --- *)

(* Get all live locals (those with valid val_ids) as (name, val_id) pairs,
   in a stable order (reversed to get original insertion order) *)
let live_locals (ctx: func_ctx): (string * val_id) list =
  (* Use List.rev to get stable order, then dedup keeping first occurrence *)
  let seen = Hashtbl.create 16 in
  List.filter (fun (name, v) ->
    if v = val_none || Hashtbl.mem seen name then false
    else begin Hashtbl.add seen name true; true end
  ) (List.rev ctx.locals)

(* Generate the argument list for a branch: current values of the given variable names *)
let branch_args (ctx: func_ctx) (names: string list): string =
  let vals = List.map (fun name -> lookup_var ctx name) names in
  String.concat ", " (List.map val_str vals)

(* Create fresh block parameters for the given variable names, bind them, return param string *)
let make_block_params (ctx: func_ctx) (names: string list): string =
  let params = List.map (fun name ->
    let v = fresh_val ctx in
    let ty = get_local_type ctx name in
    bind_var ctx name v;
    val_str v ^ ": " ^ ty
  ) names in
  String.concat ", " params

(* --- Type mapping --- *)

let rec gen_type (ty: mono_ty): string =
  match ty with
  | MonoUnit -> "unit"
  | MonoBoolean -> "bool"
  | MonoInteger (Unsigned, Width8) -> "u8"
  | MonoInteger (Unsigned, Width16) -> "u16"
  | MonoInteger (Unsigned, Width32) -> "u32"
  | MonoInteger (Unsigned, Width64) -> "u64"
  | MonoInteger (Signed, Width8) -> "i8"
  | MonoInteger (Signed, Width16) -> "i16"
  | MonoInteger (Signed, Width32) -> "i32"
  | MonoInteger (Signed, Width64) -> "i64"
  | MonoInteger (_, WidthIndex) -> "index"
  | MonoInteger (_, WidthByteSize) -> "bytesize"
  | MonoSingleFloat -> "f32"
  | MonoDoubleFloat -> "f64"
  | MonoNamedType id -> "ptr<" ^ (gen_mono_id id) ^ ">"
  | MonoRegionTy _ -> "unit"
  | MonoReadRef (ty, _) -> "ref<" ^ (gen_type ty) ^ ", %S>"
  | MonoWriteRef (ty, _) -> "refmut<" ^ (gen_type ty) ^ ", %S>"
  | MonoSpan (ty, _) -> "ref<array<" ^ (gen_type ty) ^ ">, %S>"
  | MonoSpanMut (ty, _) -> "refmut<array<" ^ (gen_type ty) ^ ">, %S>"
  | MonoAddress ty -> "ptr_or_null<" ^ (gen_type ty) ^ ">"
  | MonoPointer ty -> "ptr<" ^ (gen_type ty) ^ ">"
  | MonoFnPtr (params, rt) ->
     "fnptr(" ^ (String.concat ", " (List.map gen_type params)) ^ ") -> " ^ (gen_type rt)
  | MonoRegionTyVar _ -> "unit"

let is_float_type (ty: mono_ty): bool =
  match ty with
  | MonoSingleFloat | MonoDoubleFloat -> true
  | _ -> false

let is_unit_type (ty: mono_ty): bool =
  match ty with
  | MonoUnit -> true
  | _ -> false

let is_integer_type (ty: mono_ty): bool =
  match ty with
  | MonoInteger _ -> true
  | _ -> false

(* Get the inner type for ref/refmut *)
let inner_ref_type (ty: mono_ty): mono_ty =
  match ty with
  | MonoReadRef (t, _) -> t
  | MonoWriteRef (t, _) -> t
  | _ -> internal_err "inner_ref_type: not a ref type"

(* --- Constant table: maps qident string -> mexpr --- *)
(* We collect constants during declaration processing and inline them at use sites *)
let constant_table: (string, mexpr) Hashtbl.t = Hashtbl.create 16

let gen_qident_key (n: qident): string =
  (mod_name_string (source_module_name n)) ^ "." ^ (ident_string (original_name n))

(* --- Field index resolution --- *)

(* Given a mono_id for a record type and a slot name, find the field index *)
let resolve_record_field_index (env: env) (id: mono_id) (slot_name: identifier): int =
  match get_monomorph env id with
  | Some (MonoRecordDefinition { slots = Some slots; _ }) ->
     let rec find_idx i = function
       | [] -> internal_err ("LinIRGen: field not found: " ^ (ident_string slot_name))
       | (MonoSlot (n, _)) :: rest ->
          if equal_identifier n slot_name then i
          else find_idx (i + 1) rest
     in
     find_idx 0 slots
  | _ ->
     internal_err "LinIRGen: could not resolve record monomorph for field index"

(* Given a mono_ty that's a reference to a named type, extract the mono_id *)
let extract_named_type_id (ty: mono_ty): mono_id =
  match ty with
  | MonoNamedType id -> id
  | MonoReadRef (MonoNamedType id, _) -> id
  | MonoWriteRef (MonoNamedType id, _) -> id
  | MonoPointer (MonoNamedType id) -> id
  | MonoAddress (MonoNamedType id) -> id
  | _ -> internal_err "LinIRGen: expected named type"

(* --- Expression translation --- *)

let rec gen_exp (ctx: func_ctx) (e: mexpr): val_id =
  match e with
  | MNilConstant ->
     let r = fresh_val ctx in
     emit ctx (val_str r ^ " = uconst");
     r
  | MBoolConstant b ->
     let r = fresh_val ctx in
     emit ctx (val_str r ^ " = bconst " ^ (if b then "true" else "false"));
     r
  | MIntConstant v ->
     let ty = get_type e in
     let r = fresh_val ctx in
     emit ctx (val_str r ^ " = iconst " ^ (gen_type ty) ^ " " ^ v);
     r
  | MFloatConstant v ->
     let ty = get_type e in
     let r = fresh_val ctx in
     emit ctx (val_str r ^ " = fconst " ^ (gen_type ty) ^ " " ^ v);
     r
  | MStringConstant s ->
     let raw = escaped_to_string s in
     let label = "$data_" ^ (string_of_int ctx.next_data) in
     ctx.next_data <- ctx.next_data + 1;
     ctx.data_segs <- (label, raw) :: ctx.data_segs;
     let r = fresh_val ctx in
     emit ctx (val_str r ^ " = data_ref " ^ label ^ ", " ^ (string_of_int (String.length raw)));
     r
  | MConstVar (n, _) ->
     let key = gen_qident_key n in
     (match Hashtbl.find_opt constant_table key with
      | Some expr -> gen_exp ctx expr
      | None -> internal_err ("LinIRGen: constant not found: " ^ key))
  | MParamVar (n, _) ->
     lookup_var ctx (gen_ident n)
  | MLocalVar (n, _) ->
     lookup_var ctx (gen_ident n)
  | MTemporary (n, _) ->
     lookup_var ctx (gen_ident n)
  | MConcreteFunVar (id, _) ->
     let r = fresh_val ctx in
     emit ctx (val_str r ^ " = ref_func @" ^ (gen_decl_id id));
     r
  | MGenericFunVar (id, _) ->
     let r = fresh_val ctx in
     emit ctx (val_str r ^ " = ref_func @" ^ (gen_mono_id id));
     r
  | MConcreteFuncall (id, _, args, _) ->
     let arg_vals = List.map (gen_exp ctx) args in
     let r = fresh_val ctx in
     let args_str = String.concat ", " (List.map val_str arg_vals) in
     emit ctx (val_str r ^ " = call @" ^ (gen_decl_id id) ^ (if args_str = "" then "" else ", " ^ args_str));
     r
  | MGenericFuncall (id, args, _) ->
     let arg_vals = List.map (gen_exp ctx) args in
     let r = fresh_val ctx in
     let args_str = String.concat ", " (List.map val_str arg_vals) in
     emit ctx (val_str r ^ " = call @" ^ (gen_mono_id id) ^ (if args_str = "" then "" else ", " ^ args_str));
     r
  | MConcreteMethodCall (id, _, args, _) ->
     let arg_vals = List.map (gen_exp ctx) args in
     let r = fresh_val ctx in
     let args_str = String.concat ", " (List.map val_str arg_vals) in
     emit ctx (val_str r ^ " = call @" ^ (gen_ins_meth_id id) ^ (if args_str = "" then "" else ", " ^ args_str));
     r
  | MGenericMethodCall (_, id, args, _) ->
     let arg_vals = List.map (gen_exp ctx) args in
     let r = fresh_val ctx in
     let args_str = String.concat ", " (List.map val_str arg_vals) in
     emit ctx (val_str r ^ " = call @" ^ (gen_mono_id id) ^ (if args_str = "" then "" else ", " ^ args_str));
     r
  | MFptrCall (name, args, _) ->
     let fptr = lookup_var ctx (gen_ident name) in
     let arg_vals = List.map (gen_exp ctx) args in
     let r = fresh_val ctx in
     let args_str = String.concat ", " (List.map val_str arg_vals) in
     emit ctx (val_str r ^ " = call_indirect " ^ (val_str fptr) ^ (if args_str = "" then "" else ", " ^ args_str));
     r
  | MRecordConstructor (ty, fields) ->
     let mono_id = extract_named_type_id ty in
     (* Get the field order from the type definition *)
     let ordered_fields = order_record_fields ctx.env mono_id fields in
     let field_vals = List.map (gen_exp ctx) ordered_fields in
     let r = fresh_val ctx in
     let args_str = String.concat ", " (List.map val_str field_vals) in
     emit ctx (val_str r ^ " = record_new @" ^ (gen_mono_id mono_id) ^ (if args_str = "" then "" else ", " ^ args_str));
     r
  | MUnionConstructor (ty, case_name, fields) ->
     let mono_id = extract_named_type_id ty in
     let field_vals = List.map (fun (_, v) -> gen_exp ctx v) fields in
     let r = fresh_val ctx in
     let args_str = String.concat ", " (List.map val_str field_vals) in
     emit ctx (val_str r ^ " = union_new @" ^ (gen_mono_id mono_id) ^ ", " ^ (gen_ident case_name)
               ^ (if args_str = "" then "" else ", " ^ args_str));
     r
  | MSlotAccessor (expr, slot, _) ->
     let ref_val = gen_exp ctx expr in
     let expr_ty = get_type expr in
     let mono_id = extract_named_type_id (inner_ref_type expr_ty) in
     let idx = resolve_record_field_index ctx.env mono_id slot in
     let r = fresh_val ctx in
     emit ctx (val_str r ^ " = borrow_field " ^ (val_str ref_val) ^ ", " ^ (string_of_int idx));
     r
  | MPointerSlotAccessor (expr, slot, _) ->
     let ref_val = gen_exp ctx expr in
     let expr_ty = get_type expr in
     let mono_id = extract_named_type_id (inner_ref_type expr_ty) in
     let idx = resolve_record_field_index ctx.env mono_id slot in
     let r = fresh_val ctx in
     emit ctx (val_str r ^ " = borrow_field " ^ (val_str ref_val) ^ ", " ^ (string_of_int idx));
     r
  | MArrayIndex (expr, idx, _) ->
     let ref_val = gen_exp ctx expr in
     let idx_val = gen_exp ctx idx in
     let r = fresh_val ctx in
     emit ctx (val_str r ^ " = borrow_elem " ^ (val_str ref_val) ^ ", " ^ (val_str idx_val));
     r
  | MSpanIndex (expr, idx, _) ->
     let span_val = gen_exp ctx expr in
     let idx_val = gen_exp ctx idx in
     let r = fresh_val ctx in
     emit ctx (val_str r ^ " = borrow_elem " ^ (val_str span_val) ^ ", " ^ (val_str idx_val));
     r
  | MComparison (op, lhs, rhs) ->
     let lhs_ty = get_type lhs in
     let lv = gen_exp ctx lhs in
     let rv = gen_exp ctx rhs in
     let r = fresh_val ctx in
     let is_float = is_float_type lhs_ty in
     let opname = match op with
       | Equal -> if is_float then "feq" else "eq"
       | NotEqual -> if is_float then "fne" else "ne"
       | LessThan -> if is_float then "flt" else "lt"
       | LessThanOrEqual -> if is_float then "fle" else "le"
       | GreaterThan -> if is_float then "fgt" else "gt"
       | GreaterThanOrEqual -> if is_float then "fge" else "ge"
     in
     emit ctx (val_str r ^ " = " ^ opname ^ " " ^ (val_str lv) ^ ", " ^ (val_str rv));
     r
  | MConjunction (a, b) ->
     gen_short_circuit ctx a b true
  | MDisjunction (a, b) ->
     gen_short_circuit ctx a b false
  | MNegation e ->
     let v = gen_exp ctx e in
     let r = fresh_val ctx in
     emit ctx (val_str r ^ " = not " ^ (val_str v));
     r
  | MIfExpression (c, t, f) ->
     let cv = gen_exp ctx c in
     let then_bb = fresh_block ctx in
     let else_bb = fresh_block ctx in
     let merge_bb = fresh_block ctx in
     let result_ty = get_type t in
     let merge_param = fresh_val ctx in
     finish_block ctx ("br_if " ^ (val_str cv) ^ ", @" ^ then_bb ^ "(), @" ^ else_bb ^ "()");
     (* then block *)
     start_block ctx then_bb "";
     let tv = gen_exp ctx t in
     finish_block ctx ("br @" ^ merge_bb ^ "(" ^ (val_str tv) ^ ")");
     (* else block *)
     start_block ctx else_bb "";
     let fv = gen_exp ctx f in
     finish_block ctx ("br @" ^ merge_bb ^ "(" ^ (val_str fv) ^ ")");
     (* merge block *)
     start_block ctx merge_bb (val_str merge_param ^ ": " ^ (gen_type result_ty));
     merge_param
  | MCast (e, target_ty) ->
     let v = gen_exp ctx e in
     let src_ty = get_type e in
     gen_cast ctx v src_ty target_ty
  | MTypecast (e, target_ty) ->
     let v = gen_exp ctx e in
     let src_ty = get_type e in
     gen_cast ctx v src_ty target_ty
  | MDeref e ->
     let ref_val = gen_exp ctx e in
     let r = fresh_val ctx in
     emit ctx (val_str r ^ " = load_field " ^ (val_str ref_val) ^ ", 0");
     r
  | MSizeOf _ty ->
     (* Emit as iconst bytesize with a placeholder value. LinIR doesn't have
        a sizeof instruction, so we use 0 as placeholder. *)
     let r = fresh_val ctx in
     emit ctx (val_str r ^ " = iconst bytesize 0");
     r
  | MEmbed _ ->
     (* @embed is not supported in LinIR mode; emit trap *)
     let dead_bb = fresh_block ctx in
     finish_block ctx "trap";
     start_block ctx dead_bb "";
     let r = fresh_val ctx in
     emit ctx (val_str r ^ " = uconst");
     r

and gen_short_circuit (ctx: func_ctx) (a: mexpr) (b: mexpr) (is_and: bool): val_id =
  let av = gen_exp ctx a in
  let rhs_bb = fresh_block ctx in
  let merge_bb = fresh_block ctx in
  let merge_param = fresh_val ctx in
  if is_and then
    finish_block ctx ("br_if " ^ (val_str av) ^ ", @" ^ rhs_bb ^ "(), @" ^ merge_bb ^ "(" ^ (val_str av) ^ ")")
  else
    finish_block ctx ("br_if " ^ (val_str av) ^ ", @" ^ merge_bb ^ "(" ^ (val_str av) ^ "), @" ^ rhs_bb ^ "()");
  start_block ctx rhs_bb "";
  let bv = gen_exp ctx b in
  finish_block ctx ("br @" ^ merge_bb ^ "(" ^ (val_str bv) ^ ")");
  start_block ctx merge_bb (val_str merge_param ^ ": bool");
  merge_param

and gen_cast (ctx: func_ctx) (v: val_id) (src_ty: mono_ty) (target_ty: mono_ty): val_id =
  let r = fresh_val ctx in
  if is_float_type src_ty && is_integer_type target_ty then begin
    emit ctx (val_str r ^ " = ftoi " ^ (gen_type target_ty) ^ " " ^ (val_str v));
    r
  end else if is_integer_type src_ty && is_float_type target_ty then begin
    emit ctx (val_str r ^ " = itof " ^ (gen_type target_ty) ^ " " ^ (val_str v));
    r
  end else if is_float_type src_ty && is_float_type target_ty then begin
    emit ctx (val_str r ^ " = ftof " ^ (gen_type target_ty) ^ " " ^ (val_str v));
    r
  end else begin
    emit ctx (val_str r ^ " = cast " ^ (gen_type target_ty) ^ " " ^ (val_str v));
    r
  end

and order_record_fields (env: env) (id: mono_id) (fields: (identifier * mexpr) list): mexpr list =
  match get_monomorph env id with
  | Some (MonoRecordDefinition { slots = Some slots; _ }) ->
     List.map (fun (MonoSlot (slot_name, _)) ->
       match List.assoc_opt slot_name (List.map (fun (n, e) -> (n, e)) fields) with
       | Some e -> e
       | None -> internal_err ("LinIRGen: field value not found for: " ^ (ident_string slot_name))
     ) slots
  | _ ->
     (* Fallback: emit fields in the order given *)
     List.map snd fields

(* --- Statement translation --- *)

and gen_stmt (ctx: func_ctx) (stmt: mstmt): unit =
  match stmt with
  | MSkip -> ()
  | MBlock (a, b) ->
     gen_stmt ctx a;
     gen_stmt ctx b
  | MDiscarding e ->
     let _ = gen_exp ctx e in
     ()
  | MReturn e ->
     let ty = get_type e in
     if is_unit_type ty then begin
       let _ = gen_exp ctx e in
       finish_block ctx "ret_void";
       let dead_bb = fresh_block ctx in
       start_block ctx dead_bb ""
     end else begin
       let v = gen_exp ctx e in
       finish_block ctx ("ret " ^ (val_str v));
       let dead_bb = fresh_block ctx in
       start_block ctx dead_bb ""
     end
  | MLet (name, ty, body) ->
     (* Just allocate a slot; the actual value comes from MInitialAssign *)
     bind_var_with_type ctx (gen_ident name) val_none (gen_type ty);
     gen_stmt ctx body
  | MLetTmp (name, ty, expr) ->
     let v = gen_exp ctx expr in
     bind_var_with_type ctx (gen_ident name) v (gen_type ty)
  | MAssignTmp (name, expr) ->
     let v = gen_exp ctx expr in
     bind_var ctx (gen_ident name) v
  | MAssignVar (name, expr) ->
     let v = gen_exp ctx expr in
     bind_var ctx (gen_ident (local_name name)) v
  | MInitialAssign (name, expr) ->
     let v = gen_exp ctx expr in
     bind_var ctx (gen_ident (local_name name)) v
  | MAssign (lvalue, rvalue) ->
     let ref_val = gen_exp ctx lvalue in
     let rv = gen_exp ctx rvalue in
     emit ctx ("store_field " ^ (val_str ref_val) ^ ", 0, " ^ (val_str rv))
  | MIf (cond, then_s, else_s) ->
     gen_if_stmt ctx cond then_s else_s
  | MCase (e, whens, case_ref) ->
     gen_case_stmt ctx e whens case_ref
  | MWhile (cond, body) ->
     gen_while_stmt ctx cond body
  | MFor (var, start_e, end_e, body) ->
     gen_for_stmt ctx var start_e end_e body
  | MBorrow { original; rename; orig_type; body; mode; _ } ->
     gen_borrow_stmt ctx original rename orig_type body mode
  | MDestructure (bindings, expr, body) ->
     gen_destructure ctx bindings expr body

and gen_case_stmt (ctx: func_ctx) (e: mexpr) (whens: mtyped_when list) (case_ref: case_ref): unit =
  let ev = gen_exp ctx e in
  let merge_bb = fresh_block ctx in
  (* Create blocks for each when *)
  let when_bbs = List.map (fun _ -> fresh_block ctx) whens in
  (* Snapshot live locals *)
  let live = live_locals ctx in
  let var_names = List.map fst live in
  (* Build br_case *)
  let case_arms = List.map2 (fun (MTypedWhen (case_name, _, _)) bb ->
    (gen_ident case_name) ^ ": @" ^ bb ^ "(" ^ (val_str ev) ^ ")"
  ) whens when_bbs in
  let ty = get_type e in
  let mono_id = extract_named_type_id ty in
  finish_block ctx ("br_case " ^ (val_str ev) ^ ", [" ^ (String.concat ", " case_arms) ^ "]");
  (* Generate each when block *)
  List.iter2 (fun (MTypedWhen (case_name, bindings, body)) bb ->
    (* Restore locals to pre-case state *)
    let new_locals = List.filter (fun (n, _) -> not (List.mem_assoc n live)) ctx.locals in
    ctx.locals <- live @ new_locals;
    let case_param = fresh_val ctx in
    let case_ty = "ptr<" ^ (gen_mono_id mono_id) ^ "#" ^ (gen_ident case_name) ^ ">" in
    start_block ctx bb (val_str case_param ^ ": " ^ case_ty);
    (* Extract fields from the case-narrowed pointer *)
    List.iteri (fun i (MonoBinding { name = _; ty; rename }) ->
      let field_val = fresh_val ctx in
      emit ctx (val_str field_val ^ " = extract " ^ (val_str case_param) ^ ", " ^ (string_of_int i));
      bind_var_with_type ctx (gen_ident rename) field_val (gen_type ty)
    ) bindings;
    (* Free the case pointer for CasePlain *)
    (match case_ref with
     | CasePlain -> emit ctx ("free " ^ (val_str case_param))
     | CaseRef -> ());
    gen_stmt ctx body;
    let merge_args = branch_args ctx var_names in
    finish_block ctx ("br @" ^ merge_bb ^ "(" ^ merge_args ^ ")")
  ) whens when_bbs;
  let merge_params = make_block_params ctx var_names in
  start_block ctx merge_bb merge_params

and gen_borrow_stmt (ctx: func_ctx) (original: identifier) (rename: identifier) (orig_type: mono_ty) (body: mstmt) (mode: borrow_stmt_kind): unit =
  match mode with
  | Read ->
     let is_pointer = match orig_type with MonoAddress _ -> true | _ -> false in
     if is_pointer then begin
       (* For address types, just alias *)
       let orig_val = lookup_var ctx (gen_ident original) in
       bind_var ctx (gen_ident rename) orig_val;
       gen_stmt ctx body
     end else begin
       let orig_val = lookup_var ctx (gen_ident original) in
       let region = fresh_region ctx in
       let ref_val = fresh_val ctx in
       let frozen_val = fresh_val ctx in
       emit ctx (val_str ref_val ^ ", " ^ (val_str frozen_val) ^ " = borrow " ^ (val_str orig_val) ^ ", " ^ region);
       bind_var ctx (gen_ident rename) ref_val;
       gen_stmt ctx body;
       let restored = fresh_val ctx in
       emit ctx (val_str restored ^ " = unborrow " ^ (val_str ref_val) ^ ", " ^ (val_str frozen_val));
       bind_var ctx (gen_ident original) restored
     end
  | Write ->
     let is_pointer = match orig_type with MonoAddress _ -> true | _ -> false in
     if is_pointer then begin
       let orig_val = lookup_var ctx (gen_ident original) in
       bind_var ctx (gen_ident rename) orig_val;
       gen_stmt ctx body
     end else begin
       let orig_val = lookup_var ctx (gen_ident original) in
       let region = fresh_region ctx in
       let ref_val = fresh_val ctx in
       let frozen_val = fresh_val ctx in
       emit ctx (val_str ref_val ^ ", " ^ (val_str frozen_val) ^ " = borrowmut " ^ (val_str orig_val) ^ ", " ^ region);
       bind_var ctx (gen_ident rename) ref_val;
       gen_stmt ctx body;
       let restored = fresh_val ctx in
       emit ctx (val_str restored ^ " = unborrow " ^ (val_str ref_val) ^ ", " ^ (val_str frozen_val));
       bind_var ctx (gen_ident original) restored
     end
  | Reborrow ->
     let orig_val = lookup_var ctx (gen_ident original) in
     bind_var ctx (gen_ident rename) orig_val;
     gen_stmt ctx body

and gen_destructure (ctx: func_ctx) (bindings: mono_binding list) (expr: mexpr) (body: mstmt): unit =
  let ev = gen_exp ctx expr in
  let expr_ty = get_type expr in
  let mono_id = extract_named_type_id expr_ty in
  (* Borrow, load fields, unborrow, free *)
  let region = fresh_region ctx in
  let ref_val = fresh_val ctx in
  let frozen_val = fresh_val ctx in
  emit ctx (val_str ref_val ^ ", " ^ (val_str frozen_val) ^ " = borrow " ^ (val_str ev) ^ ", " ^ region);
  List.iteri (fun _i (MonoBinding { name; ty = _; rename }) ->
    let idx = resolve_record_field_index ctx.env mono_id name in
    let field_val = fresh_val ctx in
    emit ctx (val_str field_val ^ " = load_field " ^ (val_str ref_val) ^ ", " ^ (string_of_int idx));
    bind_var ctx (gen_ident rename) field_val
  ) bindings;
  let restored = fresh_val ctx in
  emit ctx (val_str restored ^ " = unborrow " ^ (val_str ref_val) ^ ", " ^ (val_str frozen_val));
  emit ctx ("free " ^ (val_str restored));
  gen_stmt ctx body

and gen_if_stmt (ctx: func_ctx) (cond: mexpr) (then_s: mstmt) (else_s: mstmt): unit =
  let cv = gen_exp ctx cond in
  let then_bb = fresh_block ctx in
  let else_bb = fresh_block ctx in
  let merge_bb = fresh_block ctx in
  (* Snapshot live locals before branching *)
  let live = live_locals ctx in
  let var_names = List.map fst live in
  finish_block ctx ("br_if " ^ (val_str cv) ^ ", @" ^ then_bb ^ "(), @" ^ else_bb ^ "()");
  (* then branch *)
  start_block ctx then_bb "";
  gen_stmt ctx then_s;
  let then_args = branch_args ctx var_names in
  finish_block ctx ("br @" ^ merge_bb ^ "(" ^ then_args ^ ")");
  (* else branch: restore locals to pre-branch state *)
  let new_locals = List.filter (fun (n, _) -> not (List.mem_assoc n live)) ctx.locals in
  ctx.locals <- live @ new_locals;
  start_block ctx else_bb "";
  gen_stmt ctx else_s;
  let else_args = branch_args ctx var_names in
  finish_block ctx ("br @" ^ merge_bb ^ "(" ^ else_args ^ ")");
  (* merge block: receive updated values *)
  let merge_params = make_block_params ctx var_names in
  start_block ctx merge_bb merge_params

and gen_while_stmt (ctx: func_ctx) (cond: mexpr) (body: mstmt): unit =
  let header_bb = fresh_block ctx in
  let body_bb = fresh_block ctx in
  let exit_bb = fresh_block ctx in
  (* Snapshot live locals *)
  let live = live_locals ctx in
  let var_names = List.map fst live in
  let entry_args = branch_args ctx var_names in
  finish_block ctx ("br @" ^ header_bb ^ "(" ^ entry_args ^ ")");
  (* header: receive loop variables, evaluate condition *)
  let header_params = make_block_params ctx var_names in
  start_block ctx header_bb header_params;
  let cv = gen_exp ctx cond in
  finish_block ctx ("br_if " ^ (val_str cv) ^ ", @" ^ body_bb ^ "(), @" ^ exit_bb ^ "()");
  (* body *)
  start_block ctx body_bb "";
  gen_stmt ctx body;
  let back_args = branch_args ctx var_names in
  finish_block ctx ("br @" ^ header_bb ^ "(" ^ back_args ^ ")");
  (* exit: receive final values from header *)
  let exit_params = make_block_params ctx var_names in
  start_block ctx exit_bb exit_params

and gen_for_stmt (ctx: func_ctx) (var: identifier) (start_e: mexpr) (end_e: mexpr) (body: mstmt): unit =
  let sv = gen_exp ctx start_e in
  let ev = gen_exp ctx end_e in
  (* Add the for variable to locals with its type *)
  bind_var_with_type ctx (gen_ident var) sv "index";
  let header_bb = fresh_block ctx in
  let body_bb = fresh_block ctx in
  let exit_bb = fresh_block ctx in
  (* Snapshot live locals including the for variable *)
  let live = live_locals ctx in
  let var_names = List.map fst live in
  let entry_args = branch_args ctx var_names in
  finish_block ctx ("br @" ^ header_bb ^ "(" ^ entry_args ^ ")");
  (* header *)
  let header_params = make_block_params ctx var_names in
  start_block ctx header_bb header_params;
  let loop_var = lookup_var ctx (gen_ident var) in
  let cond_val = fresh_val ctx in
  emit ctx (val_str cond_val ^ " = le " ^ (val_str loop_var) ^ ", " ^ (val_str ev));
  finish_block ctx ("br_if " ^ (val_str cond_val) ^ ", @" ^ body_bb ^ "(), @" ^ exit_bb ^ "()");
  (* body *)
  start_block ctx body_bb "";
  gen_stmt ctx body;
  (* Increment loop variable *)
  let cur_loop_var = lookup_var ctx (gen_ident var) in
  let one = fresh_val ctx in
  emit ctx (val_str one ^ " = iconst index 1");
  let next_var = fresh_val ctx in
  emit ctx (val_str next_var ^ " = add " ^ (val_str cur_loop_var) ^ ", " ^ (val_str one));
  bind_var ctx (gen_ident var) next_var;
  let back_args = branch_args ctx var_names in
  finish_block ctx ("br @" ^ header_bb ^ "(" ^ back_args ^ ")");
  (* exit *)
  let exit_params = make_block_params ctx var_names in
  start_block ctx exit_bb exit_params

(* --- Declaration translation --- *)

let lir_escape_string (s: string): string =
  let buf = Buffer.create (String.length s) in
  String.iter (fun c ->
    match c with
    | '\\' -> Buffer.add_string buf "\\\\"
    | '"' -> Buffer.add_string buf "\\\""
    | '\n' -> Buffer.add_string buf "\\n"
    | '\r' -> Buffer.add_string buf "\\r"
    | '\t' -> Buffer.add_string buf "\\t"
    | c ->
       let code = Char.code c in
       if code < 32 || code > 126 then begin
         Buffer.add_string buf (Printf.sprintf "\\x%02x" code)
       end else
         Buffer.add_char buf c
  ) s;
  Buffer.contents buf

let gen_function_body (env: env) (name: string) (params: mvalue_parameter list) (rt: mono_ty) (body: mstmt) (is_export: bool): string =
  let ctx = {
    next_val = 0;
    next_block = 1;
    next_region = 1;
    buf = Buffer.create 256;
    completed_blocks = [];
    cur_label = "entry";
    cur_params = "";
    locals = [];
    local_types = [];
    data_segs = [];
    next_data = 0;
    env = env;
  } in
  (* Bind parameters and save initial val_ids for the function signature *)
  let param_vals = List.map (fun (MValueParameter (n, t)) ->
    let v = fresh_val ctx in
    bind_var_with_type ctx (gen_ident n) v (gen_type t);
    (v, gen_type t)
  ) params in
  ctx.cur_params <- String.concat ", " (List.map (fun (v, t) -> val_str v ^ ": " ^ t) param_vals);
  (* Generate body *)
  gen_stmt ctx body;
  (* Finish the current block if it hasn't been terminated.
     This handles both normal unterminated blocks and dead merge blocks. *)
  finish_block ctx "unreachable";
  (* Assemble function *)
  let blocks = List.rev ctx.completed_blocks in
  let export_str = if is_export then "export " else "" in
  let rt_str = gen_type rt in
  let func_params = String.concat ", " (List.map (fun (v, t) -> val_str v ^ ": " ^ t) param_vals) in
  let func_header = export_str ^ "func @" ^ name ^ "(" ^ func_params ^ ") -> " ^ rt_str ^ " {\n" in
  let func_body = String.concat "\n" blocks in
  let data_str = String.concat "" (List.rev_map (fun (label, content) ->
    let escaped = lir_escape_string content in
    "data " ^ label ^ " = \"" ^ escaped ^ "\"\n"
  ) ctx.data_segs) in
  data_str ^ func_header ^ func_body ^ "}\n"

let rec gen_decl (env: env) (decl: mdecl): string =
  match decl with
  | MConstant (_, n, _, e) ->
     let key = (ident_string n) in
     (* For constants, we need to build the full key including module name.
        Since we don't have the module name here easily, we store by identifier name.
        The constant expression will be inlined at use sites. *)
     let _ = key in
     (* Store in constant table - use a simple name for lookup *)
     Hashtbl.replace constant_table key e;
     ""
  | MRecord _ -> ""
  | MRecordMonomorph (id, slots) ->
     let slot_strs = List.map (fun (MonoSlot (n, t)) ->
       "    " ^ (gen_ident n) ^ ": " ^ (gen_type t) ^ ","
     ) slots in
     "type " ^ (gen_mono_id id) ^ " = record {\n"
     ^ (String.concat "\n" slot_strs) ^ "\n}\n"
  | MUnion _ -> ""
  | MUnionMonomorph (id, cases) ->
     let case_strs = List.map (fun (MonoCase (n, slots)) ->
       let slot_strs = List.map (fun (MonoSlot (sn, st)) ->
         "        " ^ (gen_ident sn) ^ ": " ^ (gen_type st) ^ ","
       ) slots in
       if slots = [] then
         "    case " ^ (gen_ident n) ^ " {}"
       else
         "    case " ^ (gen_ident n) ^ " {\n" ^ (String.concat "\n" slot_strs) ^ "\n    }"
     ) cases in
     "type " ^ (gen_mono_id id) ^ " = union {\n"
     ^ (String.concat "\n" case_strs) ^ "\n}\n"
  | MFunction (id, _, params, rt, body) ->
     gen_function_body env (gen_decl_id id) params rt body false
  | MFunctionMonomorph (id, params, rt, body) ->
     gen_function_body env (gen_mono_id id) params rt body false
  | MForeignFunction (id, _, params, rt, underlying) ->
     gen_foreign_function env id params rt underlying
  | MConcreteInstance (_, _, _, methods) ->
     String.concat "\n" (List.map (fun (MConcreteMethod (id, _, params, rt, body)) ->
       gen_function_body env (gen_ins_meth_id id) params rt body false
     ) methods)
  | MMethodMonomorph (id, params, rt, body) ->
     gen_function_body env (gen_mono_id id) params rt body false

and gen_foreign_function (env: env) (id: decl_id) (params: mvalue_parameter list) (rt: mono_ty) (underlying: string): string =
  (* Generate an import declaration and a thin wrapper *)
  let import_name = underlying in
  let wrapper_name = gen_decl_id id in
  (* Build the import declaration *)
  let param_types = List.map (fun (MValueParameter (_, t)) -> gen_type t) params in
  let import_decl = "import func " ^ import_name ^ "("
                    ^ (String.concat ", " param_types) ^ "): " ^ (gen_type rt) ^ "\n" in
  (* Build the wrapper function that calls the import *)
  let ctx = {
    next_val = 0;
    next_block = 1;
    next_region = 1;
    buf = Buffer.create 256;
    completed_blocks = [];
    cur_label = "entry";
    cur_params = "";
    locals = [];
    local_types = [];
    data_segs = [];
    next_data = 0;
    env = env;
  } in
  let param_strs = List.map (fun (MValueParameter (n, t)) ->
    let v = fresh_val ctx in
    bind_var_with_type ctx (gen_ident n) v (gen_type t);
    val_str v ^ ": " ^ (gen_type t)
  ) params in
  ctx.cur_params <- String.concat ", " param_strs;
  let arg_vals = List.map (fun (MValueParameter (n, _)) ->
    lookup_var ctx (gen_ident n)
  ) params in
  let args_str = String.concat ", " (List.map val_str arg_vals) in
  if is_unit_type rt then begin
    let _ = fresh_val ctx in
    emit ctx ("%" ^ (string_of_int (ctx.next_val - 1)) ^ " = call_import @" ^ import_name
              ^ (if args_str = "" then "" else ", " ^ args_str));
    finish_block ctx "ret_void"
  end else begin
    let r = fresh_val ctx in
    emit ctx (val_str r ^ " = call_import @" ^ import_name
              ^ (if args_str = "" then "" else ", " ^ args_str));
    finish_block ctx ("ret " ^ (val_str r))
  end;
  let blocks = List.rev ctx.completed_blocks in
  let func_params = String.concat ", " param_strs in
  let func_header = "func @" ^ wrapper_name ^ "(" ^ func_params ^ ") -> " ^ (gen_type rt) ^ " {\n" in
  let func_body = String.concat "\n" blocks in
  import_decl ^ func_header ^ func_body ^ "}\n"

(* --- Module assembly --- *)

let is_type_decl (decl: mdecl): bool =
  match decl with
  | MRecordMonomorph _ | MUnionMonomorph _ -> true
  | _ -> false

let gen_lir_module (env: env) (MonoModule (name, decls)): string =
  let type_buf = Buffer.create 1024 in
  let code_buf = Buffer.create 4096 in
  let _ = name in
  (* Process constants first to populate the constant table *)
  List.iter (fun decl ->
    match decl with
    | MConstant (_, n, _, e) ->
       let mn = mod_name_string name in
       let key = mn ^ "." ^ (ident_string n) in
       Hashtbl.replace constant_table key e
    | _ -> ()
  ) decls;
  (* Generate all declarations, separating types from code *)
  List.iter (fun decl ->
    let s = gen_decl env decl in
    if s <> "" then begin
      if is_type_decl decl then begin
        Buffer.add_string type_buf s;
        Buffer.add_char type_buf '\n'
      end else begin
        Buffer.add_string code_buf s;
        Buffer.add_char code_buf '\n'
      end
    end
  ) decls;
  (* Types first, then code *)
  (Buffer.contents type_buf) ^ (Buffer.contents code_buf)
