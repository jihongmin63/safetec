From Stdlib Require Import Strings.String.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.

Inductive Op : Type :=.

Definition NW := prod nat (option nat).

Inductive Direction : Type := 
    | IN
    | OUT
    | INOUT
.

Inductive Base_type : Type :=
    | bstyp_boolean_type
    | bstyp_integer_type
    | bstyp_bitstring_type (exp : Expression)
    | bstyp_error_type (fs : list string)
    | bstyp_match_kind_type (fs : list string)
    | bstyp_enum_type (name : string) (fs : list string)
    | bstyp_record_type (args : list (string * Base_type))
    | bstyp_header_type (args : list (string * Base_type))
    | bstyp_stack_type (rho : Base_type) (n : nat)
    | bstyp_type_variable_type (X : string)
with Expression : Type :=
    | exp_booleans (b : bool)
    | exp_integers (nw : NW)
    | exp_variables (x : string) 
    | exp_array_accesses (exp1 exp2 : Expression)
    | exp_bitstring_slices (exp1 exp2 exp3 : Expression)
    | exp_unary_ops (unary : Op) (exp : Expression)
    | exp_binary_ops (binary : Op) (exp1 exp2 : Expression)
    | exp_casts (rho : Base_type) (exp : Expression)
    | exp_records (args : list (string * Expression))
    | exp_fields (exp : Expression) (f : string)
    | exp_type_members (X f : string)
    | exp_function_call (exp : Expression) (generics : list Base_type) (args : list Expression)
.

Inductive Function_type : Type :=
    | fntyp_data_type (rho : Base_type)
    | fntyp_table
    | fntyp_function_type (generics : list string) (args : list (Direction * string * Base_type)) (ret : Base_type)
    | fntyp_constructor_type (args : list (string * Function_type)) (ret : Function_type) 
.

Inductive Keys : Type :=
    | Table_keys (exp : Expression) (x : string)
.

Inductive Actions : Type :=
    | actions (x : string) (exps : list Expression) (args : list (string * Function_type))
.

Inductive Variable_declaration : Type :=
    | vardecl_constants (typ : Function_type) (x : string) (exp : Expression)
    | vardecl_initialized (typ : Function_type) (x : string) (exp : Expression)
    | vardecl_uninitialized (typ : Function_type) (x : string)
    | vardecl_instantiations (X : string) (args : list Expression) (x : string)
.

Inductive Statement : Type :=
    | st_method_call (name : Expression) (generics : list Base_type) (args : list Expression)
    | st_assignment (exp_loc exp_val : Expression)
    | st_conditional (cond_exp : Expression) (true_stmt false_stmt : Statement)
    | st_sequencing (stmts : list Statement)
    | st_exit
    | st_return_statement (exp : Expression)
    | st_varaible_declaration (decl : Variable_declaration)
.

Inductive Types_declaration : Type :=
    | tydecl_typdefs (type : Function_type) (X : string)
    | tydecl_enum (X : string) (fs : list string)
    | tydecl_error (fs : list string)
    | tydecl_match_kinds (fs : list string)
.

Inductive Objects_declaration : Type :=
    | objdecl_tables (x : string) (keys : list Keys) (acts : list Actions)
    | objdecl_controls (X : string) (vars : list (Direction * string * Function_type)) (args : list (string * Function_type)) (decls : list Declaration) (stmt : Statement)

with Declaration : Type :=
    | var_declaration (var_decl : Variable_declaration)
    | obj_declaration (obj_decl : Objects_declaration)
    | typ_declaration (typ_decl : Types_declaration)
.

Inductive L_value : Type :=
    | lv_local_variables (x : string)
    | lv_fields (lval : L_value) (f : string)
    | lv_array_elements (lval : L_value) (n : nat)
    | lv_bitstring_slices_lval (lval : L_value) (n1 n2 : nat)
.

Definition Prog := list Declaration.

Definition Location := nat.

Definition Environment := string -> Location.

Definition Store_typing_context := Location -> Function_type.

(*Definition Control_plane : Loc -> Value -> *)

Inductive Value : Type :=
    | val_boolean (b : bool)
    | val_integer (n : nat)
    | val_records (fs : list (string * Value))
    | val_header (fs : list (string * Value))
    | val_type_members (X f : string)
    | val_header_stack (ty : Function_type) (vals : list Value)
    | val_built_in_function (name : string) (args : list (Direction * string * Function_type)) (ty : Function_type)
    | val_table (loc : Location) (eps : Environment) (keys : list Keys) (acts : list Actions)
    | val_constructor_closures (eps : Environment) (args_w_directions : list (Direction * string * Function_type)) (args_ctrl : list (string * Function_type)) (decls : list Declaration) (stmt : Statement)
.

Definition Store := Location -> Value.

Inductive Signal : Type :=
    | sig_continue
    | sig_return (val : Value)
    | sig_exit
.

Inductive Typing_context : Type :=
    | tyctx_empty
    | tyctx_typing_context (x : string) (ty : Function_type) (ctx : Typing_context)
    | tyctx_constructor_type (X : string) (ty : Function_type) (ctx : Typing_context)
.

Inductive Type_definition_context : Type :=
    | tydefctx_empty
    | tydefctx_type_definition (X : string) (ty : Function_type) (ctx : Type_definition_context)
    | tydefctx_type_variable_and_definition_context (X : string) (ctx : Type_definition_context)
.

Definition Constant_context := string -> Value.