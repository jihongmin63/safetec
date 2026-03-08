From Petr4 Require Import Basics.
From Petr4 Require Import Static.

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Program.
Import ListNotations.

Fixpoint compare_list {A : Type} (l1 l2 : list A) (f : A -> A -> bool) : bool :=
    match pair l1 l2 with
    | pair (head1 :: l1') (head2 :: l2') =>
        if f head1 head2 then compare_list l1' l2' f else false
    | pair nil nil => true
    | _ => false
    end.

Definition Op_Boolean_Equality (op1 op2 : Op) : bool :=
    match pair op1 op2 with
    | pair unaryOp unaryOp => true
    | pair binaryOp binaryOp => true
    | _ => false
    end.

Fixpoint size_base (rho : Base_type) : nat :=
  match rho with
  | bstyp_bitstring_type exp => 1 + size_exp exp
  | bstyp_record_type args | bstyp_header_type args =>
      1 + fold_right (fun p acc => size_base (snd p) + acc) 0 args
  | bstyp_stack_type rho' _ => 1 + size_base rho'
  | _ => 1
  end
with size_exp (e : Expression) : nat :=
  match e with
  | exp_array_accesses e1 e2 | exp_binary_ops _ e1 e2 =>
      1 + size_exp e1 + size_exp e2
  | exp_bitstring_slices e1 e2 e3 => 1 + size_exp e1 + size_exp e2 + size_exp e3
  | exp_unary_ops _ e1 => 1 + size_exp e1
  | exp_casts rho e => 1 + size_base rho + size_exp e
  | exp_records args => 1 + fold_right (fun p acc => size_exp (snd p) + acc) 0 args
  | exp_fields e _ => 1 + size_exp e
  | exp_function_call e _ args =>
      1 + size_exp e + fold_right (fun a acc => size_exp a + acc) 0 args
  | _ => 1
  end.

Inductive compare_kind : Type :=
  | compare_base (rho1 rho2 : Base_type)
  | compare_exp (e1 e2 : Expression).

Definition size_compare (c : compare_kind) : nat :=
  match c with
  | compare_base rho1 rho2 => size_base rho1 + size_base rho2
  | compare_exp e1 e2 => size_exp e1 + size_exp e2
  end.

Program Fixpoint compare_impl (c : compare_kind) {measure (size_compare c)} : bool :=
  match c with
  | compare_base rho1 rho2 =>
      match pair rho1 rho2 with
      | pair bstyp_boolean_type bstyp_boolean_type | pair bstyp_integer_type bstyp_integer_type => true
      | pair (bstyp_bitstring_type exp1) (bstyp_bitstring_type exp2) => compare_impl (compare_exp exp1 exp2)
      | pair (bstyp_error_type fs1) (bstyp_error_type fs2) =>
          if List.length fs1 =? List.length fs2 then
              forallb (fun double => ((fst double) =? (snd double))%string) (combine fs1 fs2)
          else false
      | pair (bstyp_match_kind_type fs1) (bstyp_match_kind_type fs2) =>
          if List.length fs1 =? List.length fs2 then
              forallb (fun double => ((fst double) =? (snd double))%string) (combine fs1 fs2)
          else false
      | pair (bstyp_enum_type name1 fs1) (bstyp_enum_type name2 fs2) =>
          if List.length fs1 =? List.length fs2 then
              forallb (fun double => ((fst double) =? (snd double))%string) (combine fs1 fs2)
          else false
      | pair (bstyp_record_type args1) (bstyp_record_type args2) | pair (bstyp_header_type args1) (bstyp_header_type args2) =>
          compare_list args1 args2 (fun arg1 arg2 =>
              match pair arg1 arg2 with
              | pair (pair str1 rho1') (pair str2 rho2') => (str1 =? str2)%string && compare_impl (compare_base rho1' rho2')
              end
          )
      | pair (bstyp_stack_type rho1' n1) (bstyp_stack_type rho2' n2) =>
          (compare_impl (compare_base rho1' rho2')) && (n1 =? n2)
      | pair (bstyp_type_variable_type X1) (bstyp_type_variable_type X2) => (X1 =? X2)%string
      | _ => false
      end
  | compare_exp e1 e2 =>
      match pair e1 e2 with
      | pair (exp_booleans b1) (exp_booleans b2) => eqb b1 b2
      | pair (@exp_integers n1 wo1 _) (@exp_integers n2 wo2 _) =>
          (n1 =? n2)
          &&
          (match pair wo1 wo2 with
          | pair None None => true
          | pair (Some w1) (Some w2) => (w1 =? w2)
          | _ => false
          end)
      | pair (exp_variables x1) (exp_variables x2) => (x1 =? x2)%string
      | pair (exp_array_accesses exp1_a exp1_b) (exp_array_accesses exp2_a exp2_b) =>
          (compare_impl (compare_exp exp1_a exp2_a)) && (compare_impl (compare_exp exp1_b exp2_b))
      | pair (exp_bitstring_slices exp1_a exp1_b exp1_c) (exp_bitstring_slices exp2_a exp2_b exp2_c) =>
          (compare_impl (compare_exp exp1_a exp2_a)) && (compare_impl (compare_exp exp1_b exp2_b)) && (compare_impl (compare_exp exp1_c exp2_c))
      | pair (exp_unary_ops unary1 exp1) (exp_unary_ops unary2 exp2) =>
          (Op_Boolean_Equality unary1 unary2) && (compare_impl (compare_exp exp1 exp2))
      | pair (exp_binary_ops binary1 exp1_a exp1_b) (exp_binary_ops binary2 exp2_a exp2_b) =>
          (Op_Boolean_Equality binary1 binary2) && (compare_impl (compare_exp exp1_a exp2_a)) && (compare_impl (compare_exp exp1_b exp2_b))
      | pair (exp_casts rho1' exp1') (exp_casts rho2' exp2') =>
          (compare_impl (compare_base rho1' rho2')) && (compare_impl (compare_exp exp1' exp2'))
      | pair (exp_records args1) (exp_records args2) =>
          compare_list args1 args2 (fun arg1 arg2 =>
              match pair arg1 arg2 with
              | pair (pair str1 exp1) (pair str2 exp2) => (str1 =? str2)%string && compare_impl (compare_exp exp1 exp2)
              end
          )
      | pair (exp_fields exp1 f1) (exp_fields exp2 f2) => (compare_impl (compare_exp exp1 exp2)) && (f1 =? f2)%string
      | pair (exp_type_members X1 f1) (exp_type_members X2 f2) => (X1 =? X2)%string && (f1 =? f2)%string
      | pair (exp_function_call exp1 rhos1 args1) (exp_function_call exp2 rhos2 args2) =>
          (compare_impl (compare_exp exp1 exp2))
          &&
          compare_list rhos1 rhos2 (fun rb1 rb2 => compare_impl (compare_base rb1 rb2))
          &&
          compare_list args1 args2 (fun arg1 arg2 => compare_impl (compare_exp arg1 arg2))
      | _ => false
      end
  end.
Admit Obligations.

Definition Bstyp_Boolean_Equality (rho1 rho2 : Base_type) : bool := compare_impl (compare_base rho1 rho2).
Definition Exp_Boolean_Equality (e1 e2 : Expression) : bool := compare_impl (compare_exp e1 e2).

Definition Direction_Boolean_Equality (d1 d2 : Direction) : bool :=
    match pair d1 d2 with
    | pair IN IN | pair OUT OUT | pair INOUT INOUT => true
    | _ => false
    end.

Fixpoint size_fntyp (tau : Function_type) : nat :=
  match tau with
  | fntyp_data_type rho => 1 + size_base rho
  | fntyp_table => 1
  | fntyp_function_type _ params ret => 1 + size_base ret + fold_right (fun p acc => size_base (snd p) + acc) 0 params
  | fntyp_constructor_type params ret => 1 + size_fntyp ret + fold_right (fun p acc => size_fntyp (snd p) + acc) 0 params
  end.

Fixpoint Fntyp_go (n : nat) (p : Function_type * Function_type) : bool :=
  match n with
  | 0 => false
  | S n' =>
      let (t1, t2) := p in
      match pair t1 t2 with
      | pair (fntyp_data_type rho1) (fntyp_data_type rho2) => Bstyp_Boolean_Equality rho1 rho2
      | pair fntyp_table fntyp_table => true
      | pair (fntyp_function_type generics1 params1 ret1) (fntyp_function_type generics2 params2 ret2) =>
          if (List.length generics1 =? List.length generics2) && (List.length params1 =? List.length params2) then
              (forallb (fun double => ((fst double) =? (snd double))%string) (combine generics1 generics2))
              &&
              (forallb (fun double =>
                  match double with
                  | (pair (pair (pair dir1 str1) rho1) (pair (pair dir2 str2) rho2)) =>
                      (Direction_Boolean_Equality dir1 dir2) && (str1 =? str2)%string && (Bstyp_Boolean_Equality rho1 rho2)
                  end
              ) (combine params1 params2))
              &&
              (Bstyp_Boolean_Equality ret1 ret2)
          else false
      | pair (fntyp_constructor_type params1 ret1) (fntyp_constructor_type params2 ret2) =>
          (compare_list params1 params2 (fun arg1 arg2 =>
              match pair arg1 arg2 with
              | pair (pair str1 tau1') (pair str2 tau2') => (str1 =? str2)%string && Fntyp_go n' (pair tau1' tau2')
              end
          ))
          &&
          (Fntyp_go n' (pair ret1 ret2))
      | _ => false
      end
  end.

Definition fntyp_measure (p : Function_type * Function_type) : nat := size_fntyp (fst p) + size_fntyp (snd p).

Definition Fntyp_Boolean_Equality (tau1 tau2 : Function_type) : bool :=
  Fntyp_go (fntyp_measure (pair tau1 tau2)) (pair tau1 tau2).

Fixpoint Expression_typing_rules_in_Fixpoint (Sigma : Constant_context) (Gamma : Typing_context) (Delta : Type_definition_context) (exp : Expression) (tau : Function_type) (dir : Direction) : bool :=
    match exp with
    | exp_variables x =>
        match dir with
        | INOUT =>
            match search_Sigma Sigma x with
            | None =>
                match search_Gamma Gamma x with
                | Some tau' => Fntyp_Boolean_Equality tau tau'
                | None => false
                end
            | Some _ => false
            end
        | _ => false
        end
    | _ => false
    end.