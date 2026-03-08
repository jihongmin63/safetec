From Petr4 Require Import Basics.

From Stdlib Require Import Strings.String.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
Import ListNotations.

(* Expression Typing Rules *)

Fixpoint search_Gamma (Gamma : Typing_context) (x : string) : option Function_type :=
    match Gamma with
    | tyctx_empty => None
    | tyctx_typing_context x' ty ctx | tyctx_constructor_type x' ty ctx =>
        if (x =? x)%string then Some ty else search_Gamma ctx x
    end.

Fixpoint search_Delta (Delta : Type_definition_context) (x : string) : bool * (list (option Function_type)) :=
    match Delta with
    | tydefctx_empty => pair false nil
    | tydefctx_type_definition x' ty ctx => 
        let res := search_Delta ctx x in
        if (x =? x')%string then pair true ((Some ty) :: (snd res)) else res
    | tydefctx_type_variable_and_definition_context x' ctx =>
        let res := search_Delta ctx x in
        if (x =? x')%string then pair true (None :: (snd res)) else res
    end.

Fixpoint search_Sigma (Sigma : list (string * Value)) (x : string) : option Value :=
    match Sigma with
    | nil => None
    | cons (pair x' V) Sigma' =>
        if (x =? x')%string then Some V else search_Sigma Sigma' x
    end.

Definition name_return : string := "ret" ++ "urn".

Definition update_Gamma (Gamma : Typing_context) (x : string) (tau : Function_type) : Typing_context := tyctx_typing_context x tau Gamma.

Fixpoint update_Gamma_list (Gamma : Typing_context) (doubles : list (string * Function_type))  : Typing_context :=
    match doubles with
    | nil => Gamma
    | cons double doubles' =>
        update_Gamma_list (update_Gamma Gamma (fst double) (snd double)) doubles'
    end.

Inductive UnaryOperation : Type_definition_context -> Op -> Base_type -> Base_type -> Prop :=.
Inductive BinaryOperation : Type_definition_context -> Op -> Base_type -> Base_type -> Base_type -> Prop :=.

Inductive Legal_Casts  (Delta : Type_definition_context) : Base_type -> Function_type -> Prop :=.
Inductive Type_Simplification (Sigma : Constant_context) (Delta : Type_definition_context) : Function_type -> Function_type -> Prop :=.
Inductive Compile_time_Evaluation (Sigma : Constant_context) : Expression -> Value -> Prop :=.

Reserved Notation "Sg ',' G ',' D '⊢' e ':' t 'goes' d" (at level 80, G at level 39, D at level 39, e at level 39).
Inductive Expression_typing_rules (Sigma : Constant_context)  (Gamma : Typing_context) (Delta : Type_definition_context)
: Expression -> Function_type -> Direction -> Prop :=
    | T_Var (x : string) (tau : Function_type) :
        (search_Sigma Sigma x = None) -> 
        (search_Gamma Gamma x = Some tau) -> 
        Sigma , Gamma , Delta ⊢ (exp_variables x) : tau goes INOUT
    | T_Var_Const (x : string) (tau : Function_type) (V : Value) :
        (search_Sigma Sigma x = Some V) -> 
        (search_Gamma Gamma x = Some tau) -> 
        Sigma , Gamma , Delta ⊢ (exp_variables x) : tau goes IN
    | T_Bit (n w : nat) (Hw : w >= 1) (H : len n <= w) :
        Sigma , Gamma , Delta ⊢ (exp_integers (finite_nw n w H)) : (fntyp_data_type (bstyp_bitstring_type (exp_integers (infinite_nw w)))) goes IN
    | T_Bool (b : bool) : Sigma , Gamma , Delta ⊢ (exp_booleans b) : (fntyp_data_type bstyp_boolean_type) goes IN
    | T_Integer (n : nat) : Sigma , Gamma , Delta ⊢ (exp_integers (infinite_nw n)) : (fntyp_data_type bstyp_integer_type) goes IN
    | T_Index (exp1 exp2 : Expression) (ty : Base_type) (n : nat) (d : Direction) : forall (d2 : Direction),
        (Sigma , Gamma , Delta ⊢ exp1 : (fntyp_data_type (bstyp_stack_type ty n)) goes d) ->
        (Sigma , Gamma , Delta ⊢ exp2 : (fntyp_data_type (bstyp_bitstring_type (exp_integers (infinite_nw 32)))) goes d2) ->
        Sigma , Gamma, Delta ⊢ (exp_array_accesses exp1 exp2) : (fntyp_data_type ty) goes d
    | T_Enum (X f : string) (fs : list string) (ls : list (option Function_type)) :
        (search_Delta Delta X = pair true ls) ->
        (In (Some (fntyp_data_type (bstyp_enum_type X fs))) ls) ->
        Sigma , Gamma, Delta ⊢ (exp_type_members X f) : (fntyp_data_type (bstyp_enum_type X fs)) goes IN
    | T_Err (f : string) (fs : list string) (ls : list (option Function_type)) :
        (search_Delta Delta "error" = pair true ls) ->
        (In (Some (fntyp_data_type (bstyp_error_type fs))) ls) ->
        (In f fs) ->
        Sigma , Gamma, Delta ⊢ (exp_type_members "error" f) : (fntyp_data_type (bstyp_error_type fs)) goes IN
    | T_Match (f : string) (fs : list string) (ls : list (option Function_type)) :
        (search_Delta Delta "match_kind" = pair true ls) ->
        (In (Some (fntyp_data_type (bstyp_match_kind_type fs))) ls) ->
        (In f fs) ->
        Sigma , Gamma , Delta ⊢ (exp_type_members "match" f) : (fntyp_data_type (bstyp_match_kind_type fs)) goes IN
    | T_Cast (rho rho0 : Base_type) (exp : Expression) (tau : Function_type) (d : Direction) :
        (Sigma , Gamma , Delta ⊢ exp : (fntyp_data_type rho0) goes d) ->
        (Type_Simplification Sigma Delta (fntyp_data_type rho) tau) ->
        (Legal_Casts Delta rho0 tau) ->
        Sigma , Gamma , Delta ⊢ (exp_casts rho exp) : tau goes d
    | T_UOp (unary : Op) (exp : Expression) (rho1 rho2 : Base_type) :
        (Sigma , Gamma , Delta ⊢ exp : (fntyp_data_type rho1) goes IN) ->
        (UnaryOperation Delta unary rho1 rho2) ->
        Sigma , Gamma , Delta ⊢ (exp_unary_ops unary exp) : (fntyp_data_type rho2) goes IN
    | T_BinOp (binary : Op) (exp1 exp2 : Expression) (rho1 rho2 rho3 : Base_type) : forall (d1 d2 : Direction),
        (Sigma , Gamma , Delta ⊢ exp1 : (fntyp_data_type rho1) goes d1) ->
        (Sigma , Gamma , Delta ⊢ exp2 : (fntyp_data_type rho1) goes d2) ->
        (BinaryOperation Delta binary rho1 rho2 rho3) ->
        Sigma , Gamma , Delta ⊢ (exp_binary_ops binary exp1 exp2) : (fntyp_data_type rho3) goes IN
    | T_Memhdr (exp : Expression) (fi : string) (args : list (string * Base_type)) (typ : Base_type) (d: Direction) :
        (Sigma , Gamma , Delta ⊢ exp : fntyp_data_type (bstyp_header_type args) goes d) ->
        (In (pair fi typ) args) ->
        Sigma , Gamma , Delta ⊢ (exp_fields exp fi) : (fntyp_data_type typ) goes d 
    | T_Memrec (exp : Expression) (fi : string) (args : list (string * Base_type)) (typ : Base_type) (d : Direction):
        (Sigma , Gamma , Delta ⊢ exp : fntyp_data_type (bstyp_record_type args) goes d) ->
        (In (pair fi typ) args) ->
        Sigma , Gamma , Delta  ⊢ (exp_fields exp fi) : (fntyp_data_type typ) goes d 
    | T_Record (strings : list string) (exps : list Expression) (types : list Base_type) : forall (ds : list Direction),
        (forall x, In x (combine (combine strings exps) (combine types ds)) -> Sigma , Gamma , Delta ⊢ (snd (fst x)) : (fntyp_data_type (fst (snd x))) goes (snd (snd x))) ->
        Sigma , Gamma , Delta ⊢ (exp_records (combine strings exps)) : (fntyp_data_type (bstyp_record_type (combine strings types))) goes IN 
    | T_Slice (exp1 exp2 exp3 : Expression) (w n2 n3: nat) (d : Direction) : forall (d2 d3 : Direction),
        (Sigma , Gamma , Delta ⊢ exp1 : (fntyp_data_type (bstyp_bitstring_type (exp_integers (infinite_nw w)))) goes d) ->
        (Sigma , Gamma , Delta ⊢ exp2 : (fntyp_data_type bstyp_integer_type) goes d2) ->
        (Sigma , Gamma , Delta ⊢ exp3 : (fntyp_data_type bstyp_integer_type) goes d3) ->
        (Compile_time_Evaluation Sigma exp2 (val_integer n2)) ->
        (Compile_time_Evaluation Sigma exp3 (val_integer n3)) ->
        (0 <= n3 <= n2 /\ n2 < w) ->
        Sigma , Gamma , Delta ⊢ (exp_bitstring_slices exp1 exp2 exp3) : (fntyp_data_type (bstyp_bitstring_type (exp_integers (infinite_nw (n2 - n3 +1))))) goes d
    | T_Call (exp : Expression) (rhos : list Base_type) (generics : list string) (parameters : list (Direction * string * Base_type)) (ret ret' : Base_type) (args : list Expression) (types : list Function_type) : forall (d : Direction) (ds : list Direction),
        (Sigma , Gamma , Delta ⊢ exp : (fntyp_function_type generics parameters ret) goes d) ->
        (forall tau_pair, In tau_pair (combine (map (@snd _ _) parameters) types) -> Type_Simplification Sigma Delta (fntyp_data_type (fst tau_pair)) (snd tau_pair)) ->
        (forall taud, In taud (combine types ds) -> Sigma , Gamma , Delta ⊢ exp : (fst taud) goes (snd taud)) ->
        (Type_Simplification Sigma Delta (fntyp_data_type ret) (fntyp_data_type ret')) ->
        Sigma , Gamma , Delta ⊢ (exp_function_call exp rhos args) : (fntyp_data_type ret') goes IN
where "Sg ',' G ',' D '⊢' e ':' t 'goes' d" := (Expression_typing_rules Sg G D e t d).

Inductive act_ok (Sigma : Constant_context) (Gamma : Typing_context) (Delta : Type_definition_context) : Actions -> Prop :=.

Inductive Declaration_typing (Sigma : Constant_context) (Gamma : Typing_context) (Delta : Type_definition_context) : Declaration -> Constant_context -> Typing_context -> Type_definition_context -> Prop :=
    | Type_Const (tau : Function_type) (x : string) (exp : Expression) (tau tau' : Function_type) (v : Value) : forall (d : Direction),
        (Type_Simplification Sigma Delta tau tau') ->
        (Sigma , Gamma , Delta ⊢ exp : tau' goes d) ->
        (Compile_time_Evaluation Sigma exp v) ->
        Declaration_typing Sigma Gamma Delta (var_declaration (vardecl_constants tau x exp)) ((pair x v) :: Sigma) (update_Gamma Gamma x tau') Delta
    | Type_Var (tau tau' : Function_type) (x : string) :
        (Type_Simplification Sigma Delta tau tau') ->
        Declaration_typing Sigma Gamma Delta (var_declaration (vardecl_uninitialized tau x)) Sigma (update_Gamma Gamma x tau') Delta
    | Type_VarInit (tau tau' : Function_type) (x : string) (exp : Expression) : forall (d : Direction),
        (Type_Simplification Sigma Delta tau tau') ->
        (Sigma , Gamma , Delta ⊢ exp : tau' goes d) ->
        Declaration_typing Sigma Gamma Delta (var_declaration (vardecl_initialized tau x exp)) Sigma (update_Gamma Gamma x tau') Delta
    | Type_Inst (X x : string) (args : list Expression) (params : list (string * Function_type)) (ret : Function_type) : forall (d : Direction) (ds : list Direction),
        (Sigma , Gamma , Delta ⊢ (exp_variables X) (*C*) : (fntyp_constructor_type params ret) goes d) ->
        (forall triple, In triple (combine (combine args (map (fun param => snd param) params)) ds) -> Sigma , Gamma , Delta ⊢ (fst (fst triple)) : (snd (fst triple)) goes (snd triple)) ->
        Declaration_typing Sigma Gamma Delta (var_declaration (vardecl_instantiations X args x)) Sigma (update_Gamma Gamma x ret) Delta
    | T_TableDecl (x : string) (keys : list Keys) (acts : list Actions) (taus : list Function_type) : forall (ds1 ds2 : list Direction),
        (forall triple, In triple (combine (combine (map (fun key => match key with Table_keys key_exp key_x => key_exp end) keys) taus) ds1) -> Sigma , Gamma , Delta ⊢ (fst (fst triple)) : (snd (fst triple)) goes (snd triple)) ->
        (forall double, In double (combine (map (fun key => match key with Table_keys key_exp key_x => key_x end) keys) ds2) -> Sigma , Gamma , Delta ⊢ exp_variables (fst double) : fntyp_table goes (snd double)) ->
        (forall single, In single acts -> act_ok Sigma Gamma Delta single) ->
        Declaration_typing Sigma Gamma Delta (obj_declaration (objdecl_tables x keys acts)) Sigma (update_Gamma Gamma x fntyp_table) Delta
    | T_CtrlDecl (X : string) (vars : list (Direction * string * Base_type)) (args : list (string * Function_type)) (decls : list Declaration) (stmt : Statement) (taucs taus : list Function_type) (Sigma1 Sigma2 : Constant_context) (Gamma1 Gamma2 : Typing_context) (Delta1 : Type_definition_context) :
        (forall double, In double (combine taucs (map (fun arg => snd arg) args)) -> Type_Simplification Sigma Delta (fst double) (snd double)) ->
        (forall double, In double (combine taus (map (fun var => fntyp_data_type (snd var)) vars)) -> Type_Simplification Sigma Delta (fst double) (snd double)) ->
        (forall decl, In decl decls -> Declaration_typing Sigma (update_Gamma_list Gamma ((combine (map (fun double => fst double) args) taucs) ++ (combine (map (fun triple => snd (fst triple)) vars) taus))) Delta decl Sigma1 Gamma1 Delta1) ->
        (Statement_Typing Sigma1 (update_Gamma Gamma name_return (fntyp_data_type (bstyp_record_type nil))) Delta1 [stmt] Sigma2 Gamma2) ->
        Declaration_typing Sigma Gamma Delta (obj_declaration (objdecl_controls X (map (fun var => pair (fst var) (fntyp_data_type (snd var))) vars) args decls stmt)) Sigma (update_Gamma Gamma X (fntyp_constructor_type args (fntyp_function_type nil vars (bstyp_record_type nil)))) Delta
    | T_FuncDecl (tau : Function_type) (x : string) (Xs : list string) (params : list (Direction * string * Base_type)) (stmt : Statement) (Sigma2 : Constant_context) (Delta' : Type_definition_context) (Gamma' Gamma2 : Typing_context) (taus' : list Base_type) (ret : Base_type) :
        (update_Delta Delta Xs (map (fun X => None) Xs) = Some Delta') ->
        (forall double, In double (combine (map (fun param => fntyp_data_type (snd param)) params) taus') -> Type_Simplification Sigma Delta' (fst double) (fntyp_data_type (snd double))) ->
        (Type_Simplification Sigma Delta' tau (fntyp_data_type ret)) ->
        (update_Gamma_list Gamma ((pair name_return (fntyp_data_type ret)) :: (combine (map (fun param => snd (fst param)) params) (map (fun tau' => fntyp_data_type tau') taus'))) = Gamma') ->
        (Statement_Typing Sigma  Gamma' Delta' [stmt] Sigma2 Gamma2) ->
        Declaration_typing Sigma Gamma Delta (obj_declaration (objdecl_functions tau x Xs (map (fun param => pair (fst param) (fntyp_data_type (snd param)))params) stmt)) Sigma (update_Gamma Gamma x (fntyp_function_type Xs params ret)) Delta
with Statement_Typing (Sigma : Constant_context) (Gamma : Typing_context) (Delta : Type_definition_context) : list Statement -> Constant_context -> Typing_context -> Prop :=
    | TS_Empty : Statement_Typing Sigma Gamma Delta nil Sigma Gamma
    | TS_Exit : Statement_Typing Sigma Gamma Delta [st_exit] Sigma Gamma
    | TS_Block (stmt : Statement) (stmts : list Statement) (Sigma1 Sigma2 : Constant_context) (Gamma1 Gamma2 : Typing_context) :
        (Statement_Typing Sigma Gamma Delta [stmt] Sigma1 Gamma1) ->
        (Statement_Typing Sigma1 Gamma1 Delta stmts Sigma2 Gamma2) ->
        Statement_Typing Sigma Gamma Delta (stmt :: stmts) Sigma2 Gamma2
    | TS_Decl (var_decl : Variable_declaration) (Sigma' : Constant_context) (Gamma' : Typing_context) (Delta' : Type_definition_context) :
        (Declaration_typing Sigma Gamma Delta (var_declaration var_decl) Sigma' Gamma' Delta') ->
        Statement_Typing Sigma Gamma Delta [st_varaible_declaration var_decl] Sigma' Gamma'
    | TS_Assign (exp_loc exp_val : Expression) (tau : Function_type) : forall (d : Direction),
        (Sigma , Gamma , Delta ⊢ exp_loc : tau goes INOUT) ->
        (Sigma , Gamma , Delta ⊢ exp_val : tau goes d) ->
        Statement_Typing Sigma Gamma Delta [st_assignment exp_loc exp_val] Sigma Gamma
    | TS_Ret (exp : Expression) (tau tau' : Function_type) : forall (d : Direction),
        (Sigma , Gamma , Delta ⊢ exp : tau goes d) ->
        (search_Gamma Gamma name_return = Some tau') ->
        (Type_Simplification Sigma Delta tau' tau) ->
        Statement_Typing Sigma Gamma Delta [st_return_statement exp] Sigma Gamma
    | TS_If (exp : Expression) (stmt1 stmt2 : Statement) (Sigma1 Sigma2 : Constant_context) (Gamma1 Gamma2 : Typing_context) : forall (d : Direction),
        (Sigma , Gamma , Delta ⊢ exp : (fntyp_data_type bstyp_boolean_type) goes d) ->
        (Statement_Typing Sigma Gamma Delta [stmt1] Sigma1 Gamma1) ->
        (Statement_Typing Sigma Gamma Delta [stmt2] Sigma2 Gamma2) ->
        Statement_Typing Sigma Gamma Delta [st_conditional exp stmt1 stmt2] Sigma Gamma
    | TS_TblCall (exp : Expression) : forall (d : Direction),
        (Sigma , Gamma , Delta ⊢ exp : fntyp_table goes d) ->
        Statement_Typing Sigma Gamma Delta [st_method_call exp nil nil] Sigma Gamma
    | TS_Call (exp : Expression) (rhos : list Base_type) (args : list Expression) (tau : Function_type): forall (d : Direction),
        (Sigma , Gamma , Delta ⊢ (exp_function_call exp rhos args) : tau goes d) ->
        Statement_Typing Sigma Gamma Delta [st_method_call exp rhos args] Sigma Gamma
.

