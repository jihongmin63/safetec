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
    | Func (ty1 ty2 : type).

Inductive expr :=
    | NumE (n : nat)
    | BinE (op : binop) (exp1 exp2 : expr)
    | LetE (x : id) (exp1 exp2 : expr)
    | VarE (x : id)
    | FuncE (x : id) (ty : type) (exp : expr)
    | ApplyE (exp1 exp2 : expr).

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
where "C |- e : t" := (Typing C e t).

Inductive value :=
    | NumV (n : nat)
    | CloV (x : id) (exp : expr) (env : list (id * value)).

Definition environment := list (id * value).

Reserved Notation "C |- e ==> t" (at level 80, e at next level).
Inductive Eval : environment -> expr -> value -> Prop :=
    | E_numE : forall env n, env |- (NumE n) ==> NumV n
    | E_binE_add : forall env el er il ir,
        (env |- el ==> NumV il) -> (env |- er ==> NumV ir) -> (env |- (BinE ADD el er) ==> NumV (il + ir))
    | E_binE_mul : forall env el er il ir,
        (env |- el ==> NumV il) -> (env |- er ==> NumV ir) -> (env |- (BinE MUL el er) ==> NumV (il * ir))
    | E_letE : forall env x ep eb valp valb,
        (env |- ep ==> valp) -> (((x, valp) :: env) |- eb ==> valb) -> env |- (LetE x ep eb) ==> valb
    | E_varE : forall env x val,
        (find_id x env = Some val) -> env |- (VarE x) ==> val
    | E_funcE : forall env x ty e, env |- (FuncE x ty e) ==> (CloV x e env)
    | E_applyE : forall env ef ea x eb env_clo vala valr,
        (env |- ef ==> (CloV x eb env_clo)) -> (env |- ea ==> vala) -> (((x, vala) :: env_clo) |- eb ==> valr) -> env |- (ApplyE ef ea) ==> valr
where "C |- e ==> t" := (Eval C e t).

Fixpoint type_eq (ty1 ty2 : type) : bool := match ty1, ty2 with
| INT, INT => true
| Func ty11 ty12, Func ty21 ty22 => andb (type_eq ty11 ty21) (type_eq ty12 ty22)
| _, _ => false
end.

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
    end.

Theorem Termination_Type_Check :
forall C exp typ, (C |- exp : typ) <-> type_check C exp = Some typ.
Proof.
    intros C exp typ.
    split.
    {
        intro E. induction E; simpl; try (rewrite IHE1, IHE2); try reflexivity.
        - rewrite H. reflexivity.
        - rewrite IHE. reflexivity.
        - assert (H : forall typ, type_eq typ typ = true). {
            intro ty. induction ty.
            + reflexivity.
            + simpl. rewrite IHty1, IHty2. reflexivity.
          }
          specialize H with (typ := typ).
          rewrite H. reflexivity.
    }
    {
        generalize dependent typ. generalize dependent C.
        induction exp; intros C typ E; simpl in E.
        - injection E as E. rewrite <- E. apply T_numE.
        - destruct (type_check C exp1) eqn:E1.
            + destruct t.
                ++ destruct (type_check C exp2) eqn:E2.
                    +++ destruct t.
                        ++++ injection E as E.
                             rewrite <- E in *.
                             assert (H1 : C |- exp1 : INT). {
                                apply IHexp1. apply E1.
                             }
                             assert (H2 : C |- exp2 : INT). {
                                apply IHexp2. apply E2.
                             }
                             apply T_binE; assumption.
                        ++++ discriminate E. 
                    +++ discriminate E.
                ++ discriminate E.
            + discriminate E.
        - destruct (type_check C exp1) eqn:E1.
            + apply IHexp1 in E1. apply IHexp2 in E. apply T_letE with (typ := t); assumption.
            + discriminate E.
        - apply T_varE; assumption.
        - destruct (type_check ((x, ty) :: C) exp) eqn:E1.
            + apply IHexp in E1. injection E as E. rewrite <- E. apply T_funcE; assumption.
            + discriminate E.
        - destruct (type_check C exp1) eqn:E1.
            + destruct t.
                ++ discriminate E.
                ++ destruct (type_check C exp2) eqn:E2.
                    +++ destruct (type_eq t1 t) eqn:E3.
                        ++++ assert (H : forall ty1 ty2, type_eq ty1 ty2 = true -> ty1 = ty2). {
                                intros ty1.
                                induction ty1.
                                + intros ty2 H. destruct ty2. reflexivity. discriminate.
                                + intros ty2 H. destruct ty2. discriminate. simpl in H. f_equal.
                                  - destruct (type_eq ty1_1 ty2_1) eqn:Eb1.
                                    ++ apply IHty1_1 in Eb1. apply Eb1.
                                    ++ discriminate H.
                                  - destruct (type_eq ty1_1 ty2_1).
                                    ++ destruct (type_eq ty1_2 ty2_2) eqn:Eb2.
                                        +++ apply IHty1_2 in Eb2. apply Eb2.
                                        +++ discriminate H.
                                    ++ discriminate H.
                            }
                            apply H in E3. injection E as E. rewrite <- E.
                            apply IHexp1 in E1. apply IHexp2 in E2. rewrite <- E3 in E2.
                            apply T_applyE with (typ := t1); assumption.
                        ++++ discriminate E.
                    +++ discriminate E.
            + discriminate E.
    }
Qed.

(*
Fixpoint evaluation (env : environment) (exp : expr) : option value :=
    match exp with
    | NumE n => Some (NumV n)
    | BinE op exp1 exp2 =>
        match (evaluation env exp1), (evaluation env exp2) with
        | Some (NumV n1), Some (NumV n2) => 
            match op with
            | ADD => Some (NumV (n1 + n2))
            | MUL => Some (NumV (n1 * n2))
            end
        | _, _ => None
        end
    | LetE x exp1 exp2 =>
        match (evaluation env exp1) with
        | Some val => evaluation ((x, val) :: env) exp2
        | None => None
        end
    | VarE x => find_id x env
    | FuncE x ty exp => Some (CloV x exp env)
    | ApplyE exp1 exp2 =>
        match (evaluation env exp1), (evaluation env exp2) with
        | Some (CloV x exp env_clo), Some val => (evaluation ((x, val) :: env) exp)
        | _, _ => None
        end
    end.
Theorem Termination_Evaluation :
forall env exp val, (env |- exp ==> val) <-> evaluation C exp = Some val.
Admitted. 
*)

Theorem Determinism :
forall C exp typ1 typ2, (C |- exp : typ1) -> (C |- exp : typ2) -> typ1 = typ2.
Proof.
    intros C exp typ1 typ2 E1.
    generalize dependent typ2.
    induction E1; intros typ2 E2; inversion E2; try reflexivity.
    - apply IHE1_1 in H4. rewrite <- H4 in H5. apply IHE1_2 in H5. apply H5.
    - rewrite H in H2. injection H2 as H2. apply H2.
    - f_equal. apply IHE1 in H4. apply H4.
    - apply IHE1_1 in H2. injection H2 as _ H2. apply H2.
Qed.