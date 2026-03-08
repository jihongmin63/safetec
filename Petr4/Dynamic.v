From Petr4 Require Import Basics.

From Stdlib Require Import Strings.String.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
Import ListNotations.

Fixpoint update_Store (sig : Store) (val : Value) : Store := sig ++ [val]. 

Fixpoint lval_to_exp (lval : L_value) : Expression :=
    match lval with
    | lv_local_variables x => exp_variables x
    | lv_fields lval' f => exp_fields (lval_to_exp lval') f
    | lv_array_elements lval' n => exp_array_accesses (lval_to_exp lval') (exp_integers (infinite_nw n))
    | lv_bitstring_slices_lval lval' n1 n2 => exp_bitstring_slices (lval_to_exp lval') (exp_integers (infinite_nw n1)) (exp_integers (infinite_nw n2))
    end.

Fixpoint search_Env (eps : Environment) (x : string) : option Location :=
    match eps with
    | nil => None
    | cons (x', loc) eps' =>
        if (x =? x')%string then Some loc else search_Env eps' x
    end.

Fixpoint find_Loc (sig : Store) (loc : Location) : option Value :=
    match sig, loc with 
    | _, O => None
    | nil, _ => None
    | cons val sig', S O => Some val
    | cons val sig', S loc' => find_Loc sig' loc'
    end.

Fixpoint E_Inst_Aux (e : Environment) (args : list (string * Function_type)) : list Location :=
    let fix aux (len : Location) :=
        match len with
        | O => nil
        | S O => [len + List.length e]
        | S len' => (aux len') ++ [len + List.length e]
        end
    in aux (List.length args).

Inductive Type_Simplification : Type_definition_context -> Store -> Environment -> Function_type -> Function_type -> Prop :=
with Copy_in_Copy_out : Control_plane -> Type_definition_context -> Store -> Environment -> (list (Direction * string * Function_type * Expression)) -> Store -> (list (string * Location)) -> (list (L_value * Location)) -> Prop :=
    | CopyIN (C : Control_plane) (Delta : Type_definition_context) (sig sig' updated_sig : Store) (eps : Environment) (x : string) (tau : Function_type) (exp : Expression) (val : Value) (l : Location) :
        (Expression_Evaluation C Delta sig eps exp sig' val) ->
        (update_Store sig' val = updated_sig) ->
        (l = List.length updated_sig) ->
        Copy_in_Copy_out C Delta sig eps [(IN, x, tau, exp)] updated_sig [(x, l)] nil
    (*| CopyOut*)
    | CopyInOut (C : Control_plane) (Delta : Type_definition_context) (sig sig1 sig2 updated_sig : Store) (eps : Environment) (x : string) (tau : Function_type) (exp : Expression) (lval : L_value) (val : Value) (l : Location) :
        (L_value_Evaluation C Delta sig eps exp sig1 lval) ->
        (Expression_Evaluation C Delta sig1 eps (lval_to_exp lval) sig2 val) ->
        (update_Store sig2 val = updated_sig) ->
        (l = List.length updated_sig) ->
        Copy_in_Copy_out C Delta sig eps [(INOUT, x, tau, exp)] updated_sig [(x, l)] [(lval, l)]
with L_value_Assignment : Control_plane -> Type_definition_context -> Store -> Environment -> L_value -> Value -> Store -> Prop :=
with L_value_Evaluation : Control_plane -> Type_definition_context -> Store -> Environment -> Expression -> Store -> L_value -> Prop :=
with Expression_Evaluation : Control_plane -> Type_definition_context -> Store -> Environment -> Expression -> Store -> Value -> Prop :=
    | E_INT (C : Control_plane) (Delta : Type_definition_context) (sig : Store) (eps : Environment) {n : nat} {wo : option nat} (nw : NW n wo) : Expression_Evaluation C Delta sig eps (exp_integers nw) sig (val_integer n)
    | E_BOOL (C : Control_plane) (Delta : Type_definition_context) (sig : Store) (eps : Environment) (b : bool) : Expression_Evaluation C Delta sig eps (exp_booleans b) sig (val_boolean b)
    | E_TypMem (C : Control_plane) (Delta : Type_definition_context) (sig : Store) (eps : Environment) (X f : string) : Expression_Evaluation C Delta sig eps (exp_type_members X f) sig (val_type_members X f)
    | E_Var (C : Control_plane) (Delta : Type_definition_context) (sig : Store) (eps : Environment) (x : string) (l : Location) (val : Value) :
        (search_Env eps x = Some l) ->
        (find_Loc sig l = Some val) ->
        Expression_Evaluation C Delta sig eps (exp_variables x) sig val
    (*| E_Cast | E_Uop | E_BinOp*)
    | E_Rec (C : Control_plane) (Delta : Type_definition_context) (sig sig' : Store) (eps : Environment) (args : list (string * Expression)) (vals : list Value) :
        (forall double, In double (combine (map (fun arg => snd arg) args) vals) -> Expression_Evaluation C Delta sig eps (fst double) sig' (snd double)) ->
        Expression_Evaluation C Delta sig eps (exp_records args) sig' (val_records (combine (map (fun arg => fst arg) args) vals))
    | E_RecMem (C : Control_plane) (Delta : Type_definition_context) (sig sig' : Store) (eps : Environment) (exp : Expression) (fs_head fs_tail : list (string * Value)) (fi : string) (vali : Value) :
        (Expression_Evaluation C Delta sig eps exp sig' (val_records (fs_head ++ [(fi, vali)] ++ fs_tail))) ->
        Expression_Evaluation C Delta sig eps (exp_fields exp fi) sig' vali
    (*| E_Index | E_IndexOOB*)
    | E_HdrMem (C : Control_plane) (Delta : Type_definition_context) (sig sig' : Store) (eps : Environment) (exp : Expression) (fs_head fs_tail : list (string * Function_type * Value)) (fi : string) (taui : Function_type) (vali : Value) :
        (Expression_Evaluation C Delta sig eps exp sig' (val_header (fs_head ++ [(fi, taui, vali)] ++ fs_tail))) ->
        Expression_Evaluation C Delta sig eps (exp_fields exp fi) sig' vali
    (*| E_HdrMemUndef*)
    (*| E_Call_DeclExit (C : Control_plane) (Delta updated_Delta : Type_definition_context) (sig sig1 sig2 sig3 sig4 : Store) (eps eps_c : Environment) (exp : Expression) (rhos : list Base_type) (exps : list Expression) (generics : list string) (args : lsit (Direction * string * Function_type)) (taus' : list Function_type) (tau : Function_type) (decls : list Declaration) (stmt : Statement) (ls : list Location) (lvals : list L_value):
        (Expression_Evaluation C Delta sig eps exp sig1 (val_closures eps_c generics args tau decls stmt)) ->
        (update_Delta Delta generics rhos = Some update_Delta) ->
        (forall double, In double (combine (map (fun arg => snd arg) args) taus') -> Type_Simplification update_Delta sig eps (fst double) (snd double)) ->
        (forall quintuple, In quintuple (combine (combine (combine (combine args taus') exps) ls) lvals) -> 
            let (((((dir, x, ty), ty'), e), l), lval) := quadruple in
            Copy_in_Copy_out C Delta sig1 eps (dir, x, ty') sig2 [(x, l)] [(lval, l)]) ->
        (Expression_Evaluation C updated_Delta sig2 ((combine (map (fun arg => snd (fst arg) args)) ls) ++ eps_c) decl)*)
    (*| E_Call_StmtExit | E_CallN | E_Call | E_Slice*)
with Match_action_Evaluation : Control_plane -> string -> (list (Value * string)) -> string -> (list Expression) -> Prop :=
with Statement_Evaluation : Control_plane -> Type_definition_context -> Store -> Environment -> Statement -> Function_type -> Environment -> Signal -> Prop :=
with Declaration_Evaluation : Control_plane -> Type_definition_context -> Store -> Environment -> Declaration -> Type_definition_context -> Function_type -> Environment -> Signal -> Prop :=
    | E_Const (C : Control_plane) (Delta : Type_definition_context) (sig sig' : Store) (eps eps' : Environment) (tau : Function_type) (x : string) (exp : Expression) :
        (Declaration_Evaluation C Delta sig eps (var_declaration (vardecl_initialized tau x exp)) Delta sig' eps' sig_continue) ->
        Declaration_Evaluation C Delta sig eps (var_declaration (vardecl_constants tau x exp)) Delta sig' eps' sig_continue
    (* | E_VarDecl *)
    | E_VarInit (C : Control_plane) (Delta : Type_definition_context) (sig updated_sig : Store) (eps : Environment) (tau : Function_type) (x : string) (Exp : Expression) (val : Value) (l : Location) :
        (Expression_Evaluation C Delta sig eps exp sig' val) ->
        (update_Store sig val = updated_sig) ->
        (List.length updated_sig = l) ->
        Declaration_Evaluation C Delta sig eps (var_declaration (vardecl_initialized tau x exp)) Delta updated_sig ((x, l) :: eps) sig_continue
    (*| E_Inst (C : Control_plane) (Delta : Type_definition_context) (sig sig1 sig2 : Store) (eps eps_cc : Environment) (X x : string) (exps : list Expression) (args : list (Direction * string * Function_type)) (args_ctrl : list (string * Function_type)) (decls : list Declaration) (stmt : Statement) (valcs : list Value) (val : Value) (lcs : list Location) (l : Location) :
        (Expression_Evaluation C Delta sig eps (exp_variables X) sig1 (val_constructor_closures eps_cc args args_ctrl decls stmt)) ->
        (forall double, In double (combine exps valcs) -> Expression_Evaluation C Delta sig1 (fst double) sig2 (snd double)) ->
        (lcs = E_Inst_Aux eps_cc args_ctrl) ->
        (val = val_closures ((combine (map (fun arg_ctrl => fst arg_ctrl) args_ctrl) lcs) ++ eps_cc) nil args nil stmt) ->
        (l = 1 + List.length )
        Declaration_Evaluation C Delta sig eps (var_declaration (vardecl_instantiations X exps x)) Delta*)
.