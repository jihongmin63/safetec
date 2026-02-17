From Stdlib Require Import String.
From Stdlib Require Import List.
Import ListNotations.

Definition id := string.

Fixpoint find_id {A} (x : id) (l : list (id * A)) : option A :=
  match l with
  | [] => None
  | (y, v) :: t => if string_dec x y then Some v else find_id x t
  end.

Inductive binop :=
    | ADD
    | MUL.

Inductive type :=
    | INT
    | Func (ty1 ty2 : type)
    | REF (ty : type).

Inductive expr :=
    | NumE (n : nat)
    | BinE (op : binop) (exp1 exp2 : expr)
    | LetE (x : id) (exp1 exp2 : expr)
    | VarE (x : id)
    | FuncE (x : id) (ty : type) (exp : expr)
    | ApplyE (exp1 exp2 : expr)
    | RefE (exp : expr)
    | DerefE (exp : expr)
    | UpdateE (exp1 exp2 : expr).

Definition context := list (id * type).

Reserved Notation "C |- e : t" (at level 80, e at next level).
Inductive Typing : context -> expr -> type -> Prop :=
    | T_numE : forall C n, 
        C |- (NumE n) : INT
    | T_binE : forall C op el er,
        (C |- el : INT) -> (C |- er : INT) -> C |- (BinE op el er) : INT
    | T_letE : forall C x ep eb typ tyb,
        (C |- ep : typ) -> (((x, typ) :: C) |- eb : tyb) -> C |- (LetE x ep eb) : tyb
    | T_varE : forall C x ty, 
        (find_id x C = Some ty) -> C |- (VarE x) : ty
    | T_funcE : forall C x typ eb tyb,
        (((x, typ) :: C) |- eb : tyb) -> C |- (FuncE x typ eb) : (Func typ tyb)
    | T_applyE : forall C ef ea typ tyb,
        (C |- ef : (Func typ tyb)) -> (C |- ea : typ) -> C |- (ApplyE ef ea) : tyb
    | T_refE : forall C e ty, (C |- e : ty) -> (C |- (RefE e) : (REF ty))
    | T_derefE : forall C e ty, (C |- e : (REF ty)) -> (C |- (DerefE e) : ty)
    | T_updateE : forall C el er ty,
        (C |- el : (REF ty)) -> (C |- er : ty) -> (C |- UpdateE el er : ty)
where "C |- e : t" := (Typing C e t).

Fixpoint type_eq (ty1 ty2 : type) : bool := match ty1, ty2 with
| INT, INT => true
| Func ty11 ty12, Func ty21 ty22 => andb (type_eq ty11 ty21) (type_eq ty12 ty22)
| REF ty1, REF ty2 => type_eq ty1 ty2
| _, _ => false
end.

Theorem Type_Eq_is_valid1 : forall ty1 ty2, type_eq ty1 ty2 = true <-> ty1 = ty2.
Proof.
    intro ty1. induction ty1; intro ty2.
    {
        split.
        + destruct ty2; intro E; try (simpl in E; discriminate E); reflexivity.
        + destruct ty2;  intro E; try (simpl in E; discriminate E); reflexivity.
    }
    {
        split.
        + destruct ty2; intro E; try (simpl in E; discriminate E).
          - simpl in E.
            destruct (type_eq ty1_1 ty2_1) eqn:E1; try (discriminate E).
            destruct (type_eq ty1_2 ty2_2) eqn:E2; try (discriminate E).
            rewrite IHty1_1 in E1. rewrite IHty1_2 in E2.
            f_equal. apply E1. apply E2.
        + destruct ty2; intro E; try (simpl in E; discriminate E).
          - injection E as E1 E2. rewrite <- IHty1_1 in E1. rewrite <- IHty1_2 in E2.
            simpl. rewrite E1, E2. reflexivity.
    }
    {
        split.
        + destruct ty2; intro E; try (simpl in E; discriminate E).
          - simpl in E. rewrite IHty1 in E. f_equal. apply E.
        + destruct ty2; intro E; try (simpl in E; discriminate E).
          - injection E as E. rewrite <- IHty1 in E. simpl. apply E.
    }
Qed.

Theorem Type_Eq_is_valid2 : forall ty, type_eq ty ty = true.
Proof.
    intro ty.
    induction ty; try reflexivity.
    - simpl. rewrite IHty1, IHty2. reflexivity.
    - simpl. rewrite IHty. reflexivity.
Qed.

Fixpoint type_check (C : context) (exp : expr) : option type :=
    match exp with
    | NumE n => Some INT
    | BinE op exp1 exp2 =>
        match (type_check C exp1), (type_check C exp2) with
        | Some INT, Some INT => Some INT
        | _, _ => None
        end
    | LetE x exp1 exp2 =>
        match (type_check C exp1) with
        | Some ty => type_check ((x, ty) :: C) exp2
        | None => None
        end
    | VarE x => find_id x C
    | FuncE x ty exp =>
        match (type_check ((x, ty) :: C) exp) with
        | Some ty_body => Some (Func ty ty_body)
        | None => None
        end
    | ApplyE exp1 exp2 =>
        match (type_check C exp1) with
        | Some (Func ty1 ty2) =>
            match (type_check C exp2) with
            | Some ty1' => if type_eq ty1 ty1' then Some ty2 else None
            | None => None
            end
        | _ => None
        end
    | RefE exp =>
        match (type_check C exp) with
        | Some ty => Some (REF ty)
        | None => None
        end
    | DerefE exp =>
        match (type_check C exp) with
        | Some (REF ty) => Some ty
        | _ => None
        end
    | UpdateE exp1 exp2 =>
        match (type_check C exp1) with
        | Some (REF ty1) =>
            match (type_check C exp2) with
            | Some ty2 =>
                if type_eq ty1 ty2 then Some ty1 else None 
            | None => None
            end
        | _ => None
        end
    end.

Theorem Termination_Type_Check :
forall C exp typ, (C |- exp : typ) <-> type_check C exp = Some typ.
Proof.
    intros C exp typ.
    split.
    {
        intro E. induction E; simpl; try rewrite IHE1, IHE2; try rewrite IHE; try (rewrite Type_Eq_is_valid2); try reflexivity.
        - apply H.
    }
    {
        generalize dependent typ.
        generalize dependent C.
        induction exp; intros C typ E; simpl in E; try (injection E as E).
        - rewrite <- E. apply T_numE.
        - destruct (type_check C exp1) eqn:E1; try (discriminate E).
          destruct t; try (discriminate E).
          destruct (type_check C exp2) eqn:E2; try (discriminate E).
          destruct t; try (discriminate E).
          injection E as E. rewrite <- E.
          apply IHexp1 in E1. apply IHexp2 in E2.
          apply T_binE; assumption.
        - destruct (type_check C exp1) eqn:E1; try (discriminate E).
          apply IHexp1 in E1. apply IHexp2 in E.
          apply T_letE with (typ := t); assumption.
        - apply T_varE; assumption.
        - destruct (type_check ((x, ty) :: C) exp) eqn:E1; try (discriminate E).
          apply IHexp in E1. injection E as E. rewrite <- E.
          apply T_funcE; assumption.
        - destruct (type_check C exp1) eqn:E1; try (discriminate E).
          destruct t; try (discriminate E).
          destruct (type_check C exp2) eqn:E2; try (discriminate E).
          apply IHexp1 in E1. apply IHexp2 in E2.
          destruct (type_eq t1 t) eqn:EQ; try discriminate E.
          injection E as E. rewrite <- E.
          rewrite Type_Eq_is_valid1 in EQ. rewrite <- EQ in E2.
          apply T_applyE with t1; assumption.
        - destruct (type_check C exp) eqn:E1; try (discriminate E).
          injection E as E. rewrite <- E. apply IHexp in E1. apply T_refE; assumption.
        - destruct (type_check C exp) eqn:E1; try (discriminate E).
          destruct t; try (discriminate E). injection E as E. rewrite <- E. apply IHexp in E1.
          apply T_derefE; assumption.
        - destruct (type_check C exp1) eqn:E1; try (discriminate E).
          destruct t; try (discriminate E).
          destruct (type_check C exp2) eqn:E2; try (discriminate E).
          apply IHexp1 in E1. apply IHexp2 in E2.
          destruct (type_eq t t0) eqn:EQ; try (discriminate E). injection E as E.
          rewrite Type_Eq_is_valid1 in EQ. rewrite <- EQ in E2.
          rewrite <- E. apply T_updateE; assumption.
    }
Qed.

Theorem Determinism_Type_Check :
forall C exp typ1 typ2, (C |- exp : typ1) -> (C |- exp : typ2) -> typ1 = typ2.
Proof.
    intros C exp typ1 typ2 E1.
    generalize dependent typ2.
    induction E1; intros typ2 E2; inversion E2; try reflexivity.
    - apply IHE1_1 in H4. rewrite H4 in IHE1_2. apply IHE1_2 in H5. apply H5.
    - rewrite H in H2. injection H2 as H2. apply H2.
    - f_equal. apply IHE1 in H4. apply H4.
    - apply IHE1_1 in H2. injection H2 as _ H2. apply H2.
    - f_equal. apply IHE1 in H1. apply H1.
    - apply IHE1 in H1. injection H1 as H1. apply H1.
    - apply IHE1_1 in H2. injection H2 as H2. apply H2.
Qed.