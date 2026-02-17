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

Inductive value :=
    | NumV (n : nat)
    | CloV (x : id) (exp : expr) (env : list (id * value))
    | LocV (loc : nat).

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
    (env ; sto |- exp ==> value ; sto1) -> (length sto = n) -> env ; sto |- (RefE exp) ==> (LocV n) ; (sto1 ++ [ value ])
  | E_derefE : forall env sto sto1 exp n value,
    (env ; sto |- exp ==> LocV n ; sto1) -> (find_nth n sto1 = Some value) -> env ; sto |- (DerefE exp) ==> value ; sto1
  | E_updateE : forall env sto sto1 sto2 sto3 el er n valr,
    (env ; sto |- el ==> (LocV n); sto1) -> (env ; sto1 |- er ==> valr ; sto2) -> (change_nth n valr sto2 = sto3) -> env ; sto |- (UpdateE el er) ==> valr ; sto3
where "C ; St |- e ==> v ; St'" := (Eval C St e v St').

(*Fixpoint evalution_w_fuel (env : environment) (st : sto) (exp : expr) (fuel : nat) : option (value * sto) :=
    match fuel with
    | 0 => None
    | S fuel' =>
        match exp with
        | NumE n => Some (NumV n, st)
        | BinE op exp1 exp2 =>
            match (evaluation_w_fuel env st exp1 fuel') with
            | Some (NumV n1, st1) =>
                match (evalutiation_w_fuel env st1 exp2 fuel') with
                | Some (NumV n2, st2) =>
                    match op with
                    | ADD => Some (NumV (n1 + n2), st2)
                    | MUL => Some (NumV (n1 * n2), st2)
                    end
                | None => None
                end
            | None => None
            end
        | LetE x exp1 exp2 =>
            match (evaluation_w_fuel env st exp1 fuel') with
            | Some (valp, st1) =>
                match (evaluation_w_fuel ((x, valp) :: env) st1 exp2 fuel') with
                | Some (valb, st2) =>
                    Some (valb, st2)
                | None => None
                end
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
            | Some ((CloV x eb env_clo), st1) =>
                match (evaluation_w_fuel env st1 exp2 fuel') with
                | Some (vala, st2) =>
                    match (evaluation_w_fuel ((x, vala) :: env_clo) st2 eb fuel') with
                    | Some (valr, st3) => Some (valr, st3)
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | RefE exp =>
            match (evaluation_w_fuel env st exp fuel') with
            | Some (LocV n, st1) =>
                if length st1 =? n then Some ((LocV n), (st1 ++ [ value ]))
                else None
            | None => None
            end
        | DerefE exp =>
            match (evaluation env sto exp fuel') with
            | Some (LocV n, st1) =>
                if 
            | None => None
            end
        | UpdateE exp1 exp2 =>
            match (evaluation_w_fuel env st exp1 fuel') with
            | Some (LocV n, st1) =>
                match (evaluation_w_fuel env st1 exp2 fuel') with
                    admit.
                end
            | None => None
            end
        end
    end.*)

(* expression과 value의 boolean equality와 iff 조건 정의해야 함*)
(*변수 정의가 조건일 때, 각 변수의 데이터 구조마다 equality를 정의해야 함*)

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
    - apply IHE1 in H1. destruct H1 as [H1_val H1]. rewrite H in H4. split. f_equal. apply H4. rewrite H1, H1_val. reflexivity.
    - apply IHE1 in H1. destruct H1 as [H1_n H1_sto]. injection H1_n as H1_n.
      rewrite <- H1_n, <- H1_sto in H4. rewrite H in H4. injection H4 as H4.
      split. apply H4. apply H1_sto.
    - apply IHE1_1 in H2. destruct H2 as [H2_n H2_sto]. rewrite H2_sto in IHE1_2. injection H2_n as H2_n.
      apply IHE1_2 in H5. destruct H5 as [H5_n H5_sto]. rewrite H5_sto, H5_n, H2_n in H. rewrite H in H8.
      split. apply H5_n. apply H8.
Qed.