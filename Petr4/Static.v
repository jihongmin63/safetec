From P4 Require Import Basics.

From Stdlib Require Import Strings.String.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.

(* Expression Typing Rules *)

Reserved Notation "Sg ',' G ',' D '⊢' e ':' t 'goes' d" (at level 80, G at level 39, D at level 39, e at level 39).

Inductive Expression_typing_rules (Sigma : Constant_context)  (Gamma : Typing_context) (Delta : Type_definition_context)
: Expression -> Function_type -> Direction -> Prop :=
    (*| T-Var | T_Var_Const | T-Bit | T-Integer*)
    | T_Integer (n : nat) : Sigma , Gamma , Delta ⊢ (exp_integers (pair n None)) : (fntyp_data_type bstyp_integer_type) goes IN
    | T_Bit (n w : nat) : Sigma , Gamma , Delta ⊢ (exp_integers (pair n (Some w))) : (fntyp_data_type (bstyp_bitstring_type (exp_integers (nw_natural lst)))) goes IN
    | T_Bool (b : bool) : Sigma , Gamma , Delta ⊢ (exp_booleans b) : (fntyp_data_type bstyp_boolean_type) goes IN
    | T_Index (exp1 exp2 : Expression) (ty : Base_type) (n : nat) (d : Direction) : forall (d2 : Direction),
        (Sigma , Gamma , Delta ⊢ exp1 : (fntyp_data_type (bstyp_stack_type ty n)) goes d) ->
        (Sigma , Gamma , Delta ⊢ exp2 : (fntyp_data_type (bstyp_bitstring_type (exp_integers 32))) goes d2) ->
        Sigma , Gamma, Delta ⊢ (exp_array_accesses exp1 exp2) : (fntyp_data_type ty) goes d
    | T_Memhdr (exp : Expression) (fi : string) (args : list (string * Base_type)) (typ : Base_type) (d: Direction) :
        (Sigma , Gamma , Delta ⊢ exp : fntyp_data_type (bstyp_header_type args) goes d) ->
        (In (pair fi typ) args) ->
        Sigma , Gamma , Delta ⊢ (exp_fields exp fi) : typ goes d 
    | T_Memrec (exp : Expression) (fi : string) (args : list (string * Base_type)) (typ : Base_type) (d : Directions):
        (Sigma , Gamma , Delta ⊢ exp : fntyp_data_type (bstyp_enum_type args) goes d) ->
        (In (pair fi typ) args) ->
        Sigma , Gamma , Delta  ⊢ (exp_fields exp fi) : typ goes d 
    | T_Record (strings : list string) (exps : list Expression) (types : list Base_type) : forall (ds : list Direction),
        (Forall2 (fun arg tyd => match arg with
            | pair fi exp => match tyd with
                | pair type d =>  Sigma , Gamma , Delta ⊢ exp : typ goes d
                end
            end
        ) (combine strings exps) (combine types d)) ->
        Sigma , Gamma , Delta ⊢ (exp_records args) : (fntyp_data_type (bstyp_record_type (combine strings types))) goes IN 

where "Sg ',' G ',' D '⊢' e ':' t 'goes' d" := (Expression_typing_rules Sg G D e t d).