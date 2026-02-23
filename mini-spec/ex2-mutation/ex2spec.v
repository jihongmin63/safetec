From Stdlib Require Import String.
From Stdlib Require Import Nat.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
Import ListNotations.

Local Open Scope nat_scope.
Local Open Scope bool_scope.

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

Theorem type_eq_is_sound :
forall ty1 ty2, type_eq ty1 ty2 = true <-> ty1 = ty2.
Proof.
    intros ty1 ty2.
    split.
    {
        generalize dependent ty2.
        induction ty1; intros ty2 E; destruct ty2; simpl in E; try (discriminate E).
        - reflexivity.
        - apply andb_true_iff in E. destruct E as [Ea Eb].
          apply IHty1_1 in Ea. apply IHty1_2 in Eb.
          f_equal. apply Ea. apply Eb.
        - apply IHty1 in E. f_equal. apply E.
    }
    {
        generalize dependent ty2.
        induction ty1; intros ty2 E; rewrite <- E; simpl.
        - reflexivity.
        - assert (H1 : ty1_1 = ty1_1). { reflexivity. }
          apply IHty1_1 in H1. rewrite H1.
          assert (H2 : ty1_2 = ty1_2). { reflexivity. }
          apply IHty1_2 in H2. rewrite H2.
          reflexivity.
        - apply IHty1. reflexivity.
    }
Qed.

Fixpoint expr_eq (exp1 exp2 : expr) : bool := match exp1, exp2 with
| NumE n1, NumE n2 => n1 =? n2
| BinE opa expa_1 expa_2, BinE opb expb_1 expb_2 =>
    match opa, opb with
    | ADD, ADD | MUL, MUL =>
        (expr_eq expa_1 expb_1) && (expr_eq expa_2 expb_2)
    | _, _ => false
    end
| LetE xa expa_1 expa_2, LetE xb expb_1 expb_2 =>
    (xa =? xb)%string && (expr_eq expa_1 expb_1) && (expr_eq expa_2 expb_2)
| VarE xa, VarE xb => (xa =? xb)%string
| FuncE xa tya expa, FuncE xb tyb expb =>
    (xa =? xb)%string && (type_eq tya tyb) && (expr_eq expa expb)
| ApplyE expa_1 expa_2, ApplyE expb_1 expb_2 => (expr_eq expa_1 expb_1) && (expr_eq expa_2 expb_2)
| RefE expa, RefE expb => expr_eq expa expb
| DerefE expa, DerefE expb => expr_eq expa expb
| UpdateE expa_1 expa_2, UpdateE expb_1 expb_2 => (expr_eq expa_1 expb_1) && (expr_eq expa_2 expb_2)
| _, _ => false
end.
Theorem expr_eq_is_sound :
forall exp1 exp2, expr_eq exp1 exp2 = true <-> exp1 = exp2.
Proof.
    intros exp1 exp2.
    split.
    {
        generalize dependent exp2.
        induction exp1; intros exp2 E; destruct exp2; try (simpl in E); try (discriminate E).
        - rewrite PeanoNat.Nat.eqb_eq in E. f_equal. apply E.
        - destruct op.
          + destruct op0; try (discriminate E).
            rewrite andb_true_iff in E. destruct E as [Ea Eb].
            apply IHexp1_1 in Ea. apply IHexp1_2 in Eb.
            f_equal. apply Ea. apply Eb.
          + destruct op0; try (discriminate E).
            rewrite andb_true_iff in E. destruct E as [Ea Eb].
            apply IHexp1_1 in Ea. apply IHexp1_2 in Eb.
            f_equal. apply Ea. apply Eb.
        - apply andb_true_iff in E. destruct E as [Eab Ec].
          apply andb_true_iff in Eab. destruct Eab as [Ea Eb].
          rewrite String.eqb_eq in Ea. apply IHexp1_1 in Eb. apply IHexp1_2 in Ec.
          f_equal. apply Ea. apply Eb. apply Ec.
        - f_equal. rewrite String.eqb_eq in E. apply E.
        - apply andb_true_iff in E. destruct E as [Eab Ec].
          apply andb_true_iff in Eab. destruct Eab as [Ea Eb].
          f_equal. apply String.eqb_eq in Ea. apply Ea.
          rewrite type_eq_is_sound in Eb. apply Eb.
          apply IHexp1 in Ec. apply Ec.
        - apply andb_true_iff in E. destruct E as [Ea Eb].
          apply IHexp1_1 in Ea. apply IHexp1_2 in Eb.
          f_equal. apply Ea. apply Eb.
        - apply IHexp1 in E. f_equal. apply E.
        - apply IHexp1 in E. f_equal. apply E.
        - apply andb_true_iff in E. destruct E as [Ea Eb].
          apply IHexp1_1 in Ea. apply IHexp1_2 in Eb.
          f_equal. apply Ea. apply Eb.
    }
    {
        generalize dependent exp2.
        induction exp1; intros exp2 E; rewrite <- E; simpl.
        - apply PeanoNat.Nat.eqb_refl.
        - destruct op.
          + assert (H : forall x : expr, x = x). { intro x. reflexivity. }
            apply andb_true_iff. split.
            apply (IHexp1_1 exp1_1 (H exp1_1)).
            apply (IHexp1_2 exp1_2 (H exp1_2)).
          + assert (H : forall x : expr, x = x). { intro x. reflexivity. }
            apply andb_true_iff. split.
            apply (IHexp1_1 exp1_1 (H exp1_1)).
            apply (IHexp1_2 exp1_2 (H exp1_2)).
        - assert (H : forall exp : expr, exp = exp). { intro exp. reflexivity. }
          rewrite andb_true_iff. split.
          rewrite andb_true_iff. split.
          apply String.eqb_refl.
          apply IHexp1_1. apply H.
          apply IHexp1_2. apply H.
        - apply String.eqb_refl.
        - assert (H : forall exp : expr, exp = exp). { intro exp. reflexivity. }
          rewrite andb_true_iff. split.
          rewrite andb_true_iff. split.
          apply String.eqb_refl.
          apply type_eq_is_sound. reflexivity.
          apply IHexp1. apply H.
        - assert (H : forall exp : expr, exp = exp). { intro exp. reflexivity. } rewrite andb_true_iff. split.
          apply IHexp1_1. apply H.
          apply IHexp1_2. apply H.
        - assert (H : forall exp : expr, exp = exp). { intro exp. reflexivity. } apply IHexp1. apply H.
        - assert (H : forall exp : expr, exp = exp). { intro exp. reflexivity. } apply IHexp1. apply H.
        - assert (H : forall exp : expr, exp = exp). { intro exp. reflexivity. }
          rewrite andb_true_iff. split.
          apply IHexp1_1. apply H.
          apply IHexp1_2. apply H.
    }
Qed.

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

Inductive value :=
    | NumV (n : nat)
    | CloV (x : id) (exp : expr) (env : list (id * value))
    | LocV (loc : nat).

Fixpoint val_eq (val1 val2 : value) (fuel : nat) : bool := 
    match fuel with
    | 0 => false
    | S fuel' =>
        match val1, val2 with
        | NumV n1, NumV n2 => n1 =? n2
        | LocV loc1, LocV loc2 => loc1 =? loc2
        | CloV x1 exp1 env1, CloV x2 exp2 env2 =>
            let env_comp := (length env1 =? length env2) && forallb (fun x => match x with
                | ((xa, vala), (xb, valb)) => ((xa =? xb)%string && (val_eq vala valb fuel'))
                end
            ) (combine env1 env2) in
            (x1 =? x2)%string && (expr_eq exp1 exp2) && env_comp
        | _, _ => false
        end
    end.
Theorem val_eq_sound : forall fuel val1 val2,
  val_eq val1 val2 fuel = true -> val1 = val2.
Proof.
    intro fuel.
    induction fuel; intros val1 val2 E.
    - simpl in E. discriminate E.
    - induction val1; destruct val2; simpl in E; try (discriminate E).
      + f_equal. apply PeanoNat.Nat.eqb_eq in E. apply E.
      + apply andb_true_iff in E. destruct E as [Ea Ebc].
        apply andb_true_iff in Ea. destruct Ea as [Estr Eexpr].
        apply andb_true_iff in Ebc. destruct Ebc as [Elen Etail].
        f_equal. apply String.eqb_eq in Estr. apply Estr.
        apply expr_eq_is_sound. apply Eexpr.
        assert (H : (Datatypes.length env =? Datatypes.length env0) && (forallb
        (fun x : string * value * (string * value) =>
        let (y, y0) := x in
        let (xa, vala) := y in
        let (xb, valb) := y0 in (xa =? xb)%string && val_eq vala valb fuel)
        (combine env env0)) = true). { rewrite Elen. rewrite Etail. reflexivity. }
        assert (IH : forall env env0, (Datatypes.length env =? Datatypes.length env0) && (forallb
        (fun x : string * value * (string * value) =>
        let (y, y0) := x in
        let (xa, vala) := y in
        let (xb, valb) := y0 in (xa =? xb)%string && val_eq vala valb fuel)
        (combine env env0)) = true -> env = env0). { 
            intros env1.
            induction env1; intros env2 E; apply andb_true_iff in E; destruct E as [Hlen Htail].
            - apply PeanoNat.Nat.eqb_eq in Hlen. destruct env2; try (discriminate Hlen). reflexivity.
            - destruct env2; try (discriminate Hlen). simpl in Hlen.
              simpl in Htail. apply (andb_true_iff (let (xa, vala) := a in let (xb, valb) := p in (xa =? xb)%string && val_eq vala valb fuel)) in Htail.
              destruct Htail as [Hhead Htail].
              assert (H' : (Datatypes.length env1 =? Datatypes.length env2) &&
                forallb
                (fun x : string * value * (string * value) =>
                let (y, y0) := x in
                let (xa, vala) := y in
                let (xb, valb) := y0 in (xa =? xb)%string && val_eq vala valb fuel)
                (combine env1 env2) =
                true). { rewrite Hlen, Htail. reflexivity. }
              apply IHenv1 in H'.
              f_equal.
              * destruct a as [xa vala]. destruct p as [xb valb].
                apply andb_true_iff in Hhead. destruct Hhead as [Hx Hhead].
                apply String.eqb_eq in Hx. apply IHfuel in Hhead. rewrite Hx, Hhead. reflexivity.
              * apply H'.
        }
        apply IH. apply H.
      + f_equal. apply PeanoNat.Nat.eqb_eq in E. apply E.
Qed.

Definition environment := list (id * value).
Definition sto := list value.

Fixpoint find_nth (n : nat) (l : list value) : option value :=
    match n, l with
    | 1, head :: tail => Some head
    | S m, head :: tail => find_nth m tail
    | _, _ => None
    end.

Fixpoint change_nth (n : nat) (val : value) (l : list value) : list value :=
    match l with
    | head :: tail =>
        match n with
        | 0 | 1 => [ val ]
        | S m => head :: (change_nth m val tail)
        end
    | [] => []
    end.

Reserved Notation "C ; St |- e ==> v ; St'"  (at level 80, St at next level, e at next level, v at next level).
Inductive Eval : environment -> sto -> expr -> value -> sto -> Prop :=
  | E_numE : forall env sto n,  env ; sto |- (NumE n) ==> (NumV n) ; sto
  | E_binE_add : forall env sto sto1 sto2 el er il ir,
    (env ; sto |- el ==> (NumV il) ; sto1) -> (env ; sto1 |- er ==> (NumV ir) ; sto2) -> (env ; sto |- (BinE ADD el er) ==> (NumV (il + ir)) ; sto2)
  | E_binE_mul : forall env sto sto1 sto2 el er il ir,
    (env ; sto |- el ==> (NumV il) ; sto1) -> (env ; sto1 |- er ==> (NumV ir) ; sto2) -> (env ; sto |- (BinE MUL el er) ==> (NumV (il * ir)) ; sto2)
  | E_letE : forall env sto sto1 sto2 x ep eb valp valb,
    (env ; sto |- ep ==> valp ; sto1) -> (((x, valp) :: env) ; sto1 |- eb ==> valb ; sto2) -> (env ; sto |- (LetE x ep eb) ==> valb ; sto2)
  | E_varE : forall env sto x value,
    (find_id x env = Some value) -> env ; sto |- (VarE x) ==> value ; sto
  | E_funcE : forall env sto x ty exp, env ; sto |- (FuncE x ty exp) ==> (CloV x exp env) ; sto
  | E_applyE : forall env env_clo sto sto1 sto2 sto3 x ef ea eb valr vala,
    (env ; sto |- ef ==> (CloV x eb env_clo) ; sto1) -> (env ; sto1 |- ea ==> vala ; sto2) -> (((x, vala) :: env_clo) ; sto2 |- eb ==> valr ; sto3) -> env ; sto |- (ApplyE ef ea) ==> valr ; sto3
  | E_refE : forall env sto sto1 exp n value,
    (env ; sto |- exp ==> value ; sto1) -> (length sto1 = n) -> env ; sto |- (RefE exp) ==> (LocV n) ; (sto1 ++ [ value ])
  | E_derefE : forall env sto sto1 exp n value,
    (env ; sto |- exp ==> LocV n ; sto1) -> (find_nth n sto1 = Some value) -> env ; sto |- (DerefE exp) ==> value ; sto1
  | E_updateE : forall env sto sto1 sto2 sto3 el er n valr,
    (env ; sto |- el ==> (LocV n); sto1) -> (env ; sto1 |- er ==> valr ; sto2) -> (change_nth n valr sto2 = sto3) -> env ; sto |- (UpdateE el er) ==> valr ; sto3
where "C ; St |- e ==> v ; St'" := (Eval C St e v St').

Fixpoint evaluation_w_fuel (env : environment) (st : sto) (exp : expr) (fuel : nat) : option (value * sto) :=
    match fuel with
    | 0 => None
    | S fuel' =>
        match exp with
        | NumE n => Some (NumV n, st)
        | BinE op exp1 exp2 =>
            match (evaluation_w_fuel env st exp1 fuel') with
            | Some (NumV n1, st1) =>
                match (evaluation_w_fuel env st1 exp2 fuel') with
                | Some (NumV n2, st2) =>
                    match op with
                    | ADD => Some (NumV (n1 + n2), st2)
                    | MUL => Some (NumV (n1 * n2), st2)
                    end
                | _ => None
                end
            | _ => None
            end
        | LetE x exp1 exp2 =>
            match (evaluation_w_fuel env st exp1 fuel') with
            | Some (valp, st1) =>
                evaluation_w_fuel ((x, valp) :: env) st1 exp2 fuel'
            | None => None
            end
        | VarE x =>
            match find_id x env with
            | Some val => Some (val, st)
            | None => None
            end
        | FuncE x ty exp => Some ((CloV x exp env), st)
        | ApplyE exp1 exp2 =>
            match (evaluation_w_fuel env st exp1 fuel') with
            | Some (CloV x eb env_clo, st1) =>
                match (evaluation_w_fuel env st1 exp2 fuel') with
                | Some (vala, st2) =>
                    evaluation_w_fuel ((x, vala) :: env_clo) st2 eb fuel'
                | None => None
                end
            | _ => None
            end
        | RefE exp =>
            match (evaluation_w_fuel env st exp fuel') with
            | Some (v, st1) =>
                Some (LocV (length st1), st1 ++ [ v ])
            | None => None
            end
        | DerefE exp =>
            match (evaluation_w_fuel env st exp fuel') with
            | Some (LocV n, st1) =>
                match (find_nth n st1) with
                | Some val => Some (val, st1)
                | None => None
                end 
            | _ => None
            end
        | UpdateE exp1 exp2 =>
            match (evaluation_w_fuel env st exp1 fuel') with
            | Some (LocV n, st1) =>
                match (evaluation_w_fuel env st1 exp2 fuel') with
                | Some (valr, st2) => Some (valr, change_nth n valr st2)
                | None => None
                end
            | _ => None
            end
        end
    end.

Theorem Termination_evalution_w_fuel :
forall n exp env val st1 st2, evaluation_w_fuel env st1 exp n = Some (val, st2) -> (env ; st1 |- exp ==> val ; st2).
Proof.
    intro fuel.
    induction fuel.
    - intros exp env val st1 st2 E. simpl in E. discriminate E.
    - intro exp. induction exp; intros env val st1 st2 E; simpl in E.
      + injection E as E1 E2. rewrite <- E1, <- E2. apply E_numE.
      + destruct (evaluation_w_fuel env st1 exp1 fuel) eqn:E1; try (discriminate E).
        destruct p as [v st1']. destruct v; try (discriminate E).
        destruct (evaluation_w_fuel env st1' exp2 fuel) eqn:E2; try (discriminate E).
        destruct p as [v st2']. destruct v; try (discriminate E).
        destruct op.
        * apply IHfuel in E1. apply IHfuel in E2. injection E as Evalue Estate.
          rewrite <- Estate, <- Evalue.
          apply (E_binE_add env st1 st1' st2' exp1 exp2 n n0 E1 E2).
        * apply IHfuel in E1. apply IHfuel in E2. injection E as Evalue Estate.
          rewrite <- Estate, <- Evalue.
          apply (E_binE_mul env st1 st1' st2' exp1 exp2 n n0 E1 E2).
      + destruct (evaluation_w_fuel env st1 exp1 fuel) eqn:E1; try (discriminate E).
        destruct p as [valp sta]. apply IHfuel in E. apply IHfuel in E1.
        apply (E_letE _ _ sta _ _ _ _ valp _ E1 E).
      + destruct (find_id x env) eqn:E1; try (discriminate E).
        injection E as Estate. rewrite <- Estate, <- H.
        apply (E_varE _ _ _ v E1).
      + injection E as Evalue Estate. rewrite <- Evalue, <- Estate.
        apply E_funcE.
      + destruct (evaluation_w_fuel env st1 exp1 fuel) eqn:E1; try (discriminate E).
        destruct p as [valp sta]. destruct valp; try (discriminate E).
        destruct (evaluation_w_fuel env sta exp2 fuel) eqn:E2; try (discriminate E).
        destruct p as [vala stb].
        apply IHfuel in E1, E2, E.
        apply (E_applyE env env0 st1 sta stb st2 x exp1 exp2 exp val vala); assumption.
      + destruct (evaluation_w_fuel env st1 exp fuel) eqn:E1; try (discriminate E).
        destruct p as [value sta].  injection E as Evalue Estate.
        rewrite <- Estate, <- Evalue. apply IHfuel in E1.
        assert (H : (Datatypes.length sta) = (Datatypes.length sta)). { reflexivity. }
        apply (E_refE env st1 sta exp (Datatypes.length sta) value); assumption.
      + destruct (evaluation_w_fuel env st1 exp fuel) eqn:E1; try (discriminate E).
        destruct p as [v sta]. destruct v; try (discriminate E).
        destruct (find_nth loc sta) eqn:E2; try (discriminate E).
        injection E as Evalue Estate. rewrite <- Evalue, <- Estate. apply IHfuel in E1.
        apply (E_derefE env st1 sta exp loc v); assumption.
      + destruct (evaluation_w_fuel env st1 exp1 fuel) eqn:E1; try (discriminate E).
        destruct p as [v sta]. destruct v; try (discriminate E).
        destruct (evaluation_w_fuel env sta exp2 fuel) eqn:E2; try (discriminate E).
        destruct p as [valr stb]. injection E as Evalue Estate.
        rewrite <- Evalue. apply IHfuel in E1, E2.
        apply(E_updateE env st1 sta stb _ exp1 exp2 loc valr); assumption.
Qed.

Theorem Determinism_Evaluation :
forall C sto1 sto2 sto2' exp value value',
(C ; sto1 |- exp ==> value ; sto2) -> (C ; sto1 |- exp ==> value' ; sto2') -> (value = value' /\ sto2 = sto2').
Proof.
    intros C sto1 sto2 sto2' exp value value' E1.
    generalize dependent sto2'.
    generalize dependent value'.
    induction E1; intros value' sto2' E2; inversion E2.
    - split. reflexivity. reflexivity.
    - apply IHE1_1 in H3. destruct H3 as [H3_val H3_sto].
      rewrite <- H3_sto in H6. apply IHE1_2 in H6. destruct H6 as [H6_val H6_sto].
      split. injection H3_val as Val1. injection H6_val as Val2. rewrite Val1, Val2. reflexivity. apply H6_sto.
    - apply IHE1_1 in H3. destruct H3 as [H3_val H3_sto].
      rewrite <- H3_sto in H6. apply IHE1_2 in H6. destruct H6 as [H6_val H6_sto].
      split. injection H3_val as Val1. injection H6_val as Val2. rewrite Val1, Val2. reflexivity. apply H6_sto.
    - apply IHE1_1 in H6. destruct H6 as [H6_val H6_sto]. rewrite H6_val, H6_sto in IHE1_2.
      apply IHE1_2 in H7. apply H7.
    - rewrite H in H3. injection H3 as H3. split. apply H3. reflexivity.
    - split. reflexivity. reflexivity.
    - apply IHE1_1 in H1. destruct H1 as [H1_vars H1_sto].
      rewrite H1_sto in IHE1_2. apply IHE1_2 in H4. destruct H4 as [H4_val H4_sto].
      injection H1_vars as H1_x H1_eb H1_env. rewrite H1_x, H4_val, H4_sto, H1_eb, H1_env in IHE1_3.
      apply IHE1_3 in H7. apply H7.
    - apply IHE1 in H1. destruct H1 as [Hvalue Hstate]. rewrite Hstate in H. rewrite H in H4. split.
      f_equal. apply H4. f_equal. apply Hstate. f_equal. apply Hvalue.
    - apply IHE1 in H1. destruct H1 as [H1_n H1_sto]. injection H1_n as H1_n.
      rewrite <- H1_n, <- H1_sto in H4. rewrite H in H4. injection H4 as H4.
      split. apply H4. apply H1_sto.
    - apply IHE1_1 in H2. destruct H2 as [H2_n H2_sto]. rewrite H2_sto in IHE1_2. injection H2_n as H2_n.
      apply IHE1_2 in H5. destruct H5 as [H5_n H5_sto]. rewrite H5_sto, H5_n, H2_n in H. rewrite H in H8.
      split. apply H5_n. apply H8.
Qed.