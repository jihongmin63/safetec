From Stdlib Require Import String.
From Stdlib Require Import Nat.
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

Inductive globalDecl :=
    | GlobalID (x : id) (exp : expr).

Inductive program :=
    | GlobalDecl (gd : globalDecl) (p : program)
    | LocalDecl (exp : expr).

Definition context := (list (id * type) * list (id * type))%type.

Reserved Notation "C |- e : t" (at level 80, e at next level).
Inductive Typing : context -> expr -> type -> Prop :=
    | T_numE : forall C n, 
        C |- (NumE n) : INT
    | T_binE : forall C op el er,
        (C |- el : INT) -> (C |- er : INT) -> C |- (BinE op el er) : INT
    | T_letE : forall CG CL x ep eb typ tyb,
        ((CG, CL) |- ep : typ) -> ((CG, ((x, typ) :: CL)) |- eb : tyb) -> (CG, CL) |- (LetE x ep eb) : tyb
    | T_varE_global : forall CG CL x ty, 
        (find_id x CG = Some ty) -> (CG, CL) |- (VarE x) : ty
    | T_varE_local : forall CG CL x ty, 
        (find_id x CL = Some ty) -> (CG, CL) |- (VarE x) : ty
    | T_funcE : forall CG CL x typ eb tyb,
        ((CG, ((x, typ) :: CL)) |- eb : tyb) -> (CG, CL) |- (FuncE x typ eb) : (Func typ tyb)
    | T_applyE : forall C ef ea typ tyb,
        (C |- ef : (Func typ tyb)) -> (C |- ea : typ) -> C |- (ApplyE ef ea) : tyb
    | T_refE : forall C e ty, (C |- e : ty) -> (C |- (RefE e) : (REF ty))
    | T_derefE : forall C e ty, (C |- e : (REF ty)) -> (C |- (DerefE e) : ty)
    | T_updateE : forall C el er ty,
        (C |- el : (REF ty)) -> (C |- er : ty) -> (C |- UpdateE el er : ty)
where "C |- e : t" := (Typing C e t).

Fixpoint type_check (C : context) (exp : expr) : option type :=
    match exp with
    | NumE n => Some INT
    | BinE _ exp1 exp2 =>
        match (type_check C exp1), (type_check C exp2) with
        | Some INT, Some INT => Some INT
        | _, _ => None
        end
    | LetE x exp1 exp2 =>
        let (CG, CL) := C in
        match type_check (CG, CL) exp1 with
        | Some typ => type_check (CG, (x, typ) :: CL) exp2
        | None => None
        end
    | VarE x =>
        (*erroneous case*)
        let (CG, CL) := C in
        match find_id x CG with
        | Some ty => Some ty
        | None => find_id x CL
        end
    | FuncE x typ exp =>
        let (CG, CL) := C in
        match type_check (CG, (x, typ) :: CL) exp with
        | Some tyb => Some (Func typ tyb)
        | None => None
        end
    | ApplyE exp1 exp2 =>
        match type_check C exp1 with
        | Some (Func typ tyb) => 
            match type_check C exp2 with
            | Some ty => if type_eq typ ty then Some tyb else None
            | None => None
            end
        | _ => None
        end
    | RefE exp =>
        match type_check C exp with
        | Some ty => Some (REF ty)
        | None => None
        end
    | DerefE exp =>
        match type_check C exp with
        | Some (REF ty) => Some ty
        | _ => None
        end
    | UpdateE exp1 exp2 =>
        match type_check C exp1 with
        | Some (REF ty1) =>
            match type_check C exp2 with
            | Some ty2 => if type_eq ty1 ty2 then Some ty1 else None
            | None => None
            end
        | _ => None
        end
    end.

Theorem Termination_Type_Check :
forall C exp typ, type_check C exp = Some typ -> (C |- exp : typ).
Proof.
    intros C exp. generalize dependent C.
    induction exp; intros C typ E; simpl in E.
    - injection E as E. rewrite <- E. apply T_numE.
    - destruct (type_check C exp1) eqn:E1; try (discriminate E).
      destruct t; try (discriminate E).
      destruct (type_check C exp2) eqn:E2; try (discriminate E).
      destruct t; try (discriminate E).
      apply IHexp1 in E1. apply IHexp2 in E2. injection E as E. rewrite <- E.
      apply T_binE; assumption.
    - destruct C as [CG CL].
      destruct (type_check (CG, CL) exp1) eqn:E1; try (discriminate E).
      apply IHexp1 in E1. apply IHexp2 in E.
      apply T_letE with t; assumption.
    - destruct C as [CG CL].
      destruct (find_id x CG) eqn:EG.
      + injection E as E. rewrite <- E. apply T_varE_global; assumption.
      + apply T_varE_local; assumption.
    - destruct C as [CG CL].
      destruct (type_check (CG, (x, ty) :: CL) exp) eqn:Ef; try (discriminate E).
      injection E as E. rewrite <- E. apply IHexp in Ef. 
      apply T_funcE; assumption.
    - destruct (type_check C exp1) eqn:E1; try (discriminate E).
      destruct t; try (discriminate E).
      destruct (type_check C exp2) eqn:E2; try (discriminate E).
      destruct (type_eq t1 t) eqn:Eb; try (discriminate E).
      rewrite Type_Eq_is_valid1 in Eb. rewrite <- Eb in E2. apply IHexp1 in E1. apply IHexp2 in E2.
      injection E as E. rewrite <- E. apply T_applyE with t1; assumption.
    - destruct (type_check C exp) eqn:E1; try (discriminate E).
      injection E as E. rewrite <- E. apply IHexp in E1.
      apply T_refE; assumption.
    - destruct (type_check C exp) eqn:E1; try (discriminate E).
      destruct t; try (discriminate E).
      injection E as E. rewrite <- E. apply IHexp in E1.
      apply T_derefE; assumption.
    - destruct (type_check C exp1) eqn:E1; try (discriminate E).
      destruct t; try (discriminate E).
      destruct (type_check C exp2) eqn:E2; try (discriminate E).
      destruct (type_eq t t0) eqn:Eb; try (discriminate E).
      rewrite Type_Eq_is_valid1 in Eb. injection E as E. apply IHexp1 in E1. apply IHexp2 in E2.
      rewrite <- E. rewrite <- Eb in E2.
      apply T_updateE; assumption.
Qed.

Reserved Notation "C |- p ; t" (at level 80, p at next level, t at next level).

Inductive Typing_Prog : context -> program -> type -> Prop :=
    | T_P_expr : forall C e ty, (C |- e : ty) -> (C |- (LocalDecl e) ; ty)
    | T_P_decl : forall CG CL x e p ty typ,
        ((CG, CL) |- e : ty) -> ((((x, ty) :: CG), CL) |- p ; typ) -> (CG, CL) |- (GlobalDecl (GlobalID x e) p) ; typ
where "C |- p ; t" := (Typing_Prog C p t).

Fixpoint type_check_prog (C : context) (p : program) : option type :=
    match p with
    | GlobalDecl gd p' =>
        let (CG, CL) := C in
        match gd with
        | GlobalID x exp =>
            match type_check C exp with
            | Some ty =>
                type_check_prog ((x, ty) :: CG, CL) p'
            | None => None
            end
        end
    | LocalDecl exp => type_check C exp
    end.

Theorem Termination_Type_Check_Program :
forall C p ty, type_check_prog C p = Some ty -> C |- p ; ty.
Proof.
    intros C p. generalize dependent C.
    induction p; intros C ty E; simpl in E.
    - destruct C as [CG CL]. destruct gd as [x exp].
      destruct (type_check (CG, CL) exp) eqn:E1; try (discriminate E).
      apply IHp in E. apply Termination_Type_Check in E1.
      apply T_P_decl with t; assumption.
    - apply Termination_Type_Check in E. apply T_P_expr; assumption.
Qed.

Inductive value :=
    | NumV (n : nat)
    | CloV (x : id) (exp : expr) (env : (list (id * value) * list (id * value))%type)
    | LocV (loc : nat).

Definition environment := (list (id * value) * list (id * value))%type.
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
  | E_letE : forall envG envL sto sto1 sto2 x ep eb valp valb,
    ((envG, envL) ; sto |- ep ==> valp ; sto1) -> ((envG, ((x, valp) :: envL)) ; sto1 |- eb ==> valb ; sto2) -> ((envG, envL) ; sto |- (LetE x ep eb) ==> valb ; sto2)
  | E_varE_local : forall envG envL sto x value,
    (find_id x envL = Some value) -> (envG, envL) ; sto |- (VarE x) ==> value ; sto
  | E_varE_global : forall envG envL sto x value,
    (find_id x envG = Some value) -> (envG, envL) ; sto |- (VarE x) ==> value ; sto
  | E_funcE : forall env sto x ty exp, env ; sto |- (FuncE x ty exp) ==> (CloV x exp env) ; sto
  | E_applyE : forall env env_cloG env_cloL sto sto1 sto2 sto3 x ef ea eb valr vala,
    (env ; sto |- ef ==> (CloV x eb (env_cloG, env_cloL)) ; sto1) -> (env ; sto1 |- ea ==> vala ; sto2) -> ((env_cloG, ((x, vala) :: env_cloL)) ; sto2 |- eb ==> valr ; sto3) -> env ; sto |- (ApplyE ef ea) ==> valr ; sto3
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
            let (envG, envL) := env in
            match (evaluation_w_fuel (envG, envL) st exp1 fuel') with
            | Some (valp, st1) => evaluation_w_fuel (envG, (x, valp) :: envL) st1 exp2 fuel'
            | None => None
            end
        | VarE x =>
            let (envG, envL) := env in
            match (find_id x envG) with
            | Some value => Some (value, st)
            | None => 
                match (find_id x envL) with
                | Some value => Some (value, st)
                | None => None
                end
            end
        | FuncE x ty exp => Some (CloV x exp env, st)
        | ApplyE exp1 exp2 =>
            match (evaluation_w_fuel env st exp1 fuel') with
            | Some (CloV x exp env_clo, st1) =>
                let (env_cloG, env_cloL) := env_clo in
                match (evaluation_w_fuel env st1 exp2 fuel') with
                | Some (vala, st2) =>
                    evaluation_w_fuel (env_cloG, (x, vala) :: env_cloL) st2 exp fuel'
                | None => None
                end
            | _ => None
            end
        | RefE exp =>
            match evaluation_w_fuel env st exp fuel' with
            | Some (value, st1) => Some (LocV (length st1), st1 ++ [value])
            | None => None
            end
        | DerefE exp =>
            match evaluation_w_fuel env st exp fuel' with
            | Some (LocV n, st1) => 
                match find_nth n st1 with
                | Some value => Some (value, st1)
                | None => None
                end
            | _ => None
            end
        | UpdateE exp1 exp2 =>
            match evaluation_w_fuel env st exp1 fuel' with
            | Some (LocV n, st1) =>
                match evaluation_w_fuel env st1 exp2 fuel' with
                | Some (valr, st2) =>
                    Some (valr, change_nth n valr st2)
                | None => None
                end
            | _ => None
            end
        end
    end.

Theorem Termination_Evaluation :
forall fuel exp env st1 st2 val, evaluation_w_fuel env st1 exp fuel = Some (val, st2) -> env ; st1 |- exp ==> val ; st2.
Proof.
    intro fuel.
    induction fuel.
    - intros exp env st1 st2 val E. simpl in E. discriminate E.
    - intro exp. induction exp; intros env st1 st2 val E; simpl in E.
      + injection E as Evalue Estate. rewrite <- Evalue, <- Estate. apply E_numE.
      + destruct (evaluation_w_fuel env st1 exp1 fuel) eqn:E1; try (discriminate E).
        destruct p as [v sta]. destruct v; try (discriminate E).
        destruct (evaluation_w_fuel env sta exp2 fuel) eqn:E2; try (discriminate E).
        destruct p as [v stb]. destruct v; try (discriminate E).
        apply IHfuel in E1, E2.
        destruct op.
        injection E as Evalue Estate. rewrite <- Evalue, <- Estate.
        apply E_binE_add with sta; assumption.
        injection E as Evalue Estate. rewrite <- Evalue, <- Estate.
        apply E_binE_mul with sta; assumption.
      + destruct env as [envG envL].
        destruct (evaluation_w_fuel (envG, envL) st1 exp1 fuel) eqn:E1; try (discriminate E).
        destruct p as [valp sta].
        apply IHfuel in E, E1. apply E_letE with sta valp; assumption.
      + destruct env as [envG envL].
        destruct (find_id x envG) eqn:EG.
        injection E as Evalue Estate. rewrite <- Evalue, <- Estate. apply E_varE_global; assumption.
        destruct (find_id x envL) eqn:EL; try (discriminate E).
        injection E as Evalue Estate. rewrite <- Evalue, <- Estate. apply E_varE_local; assumption.
      + injection E as Evalue Estate. rewrite <- Evalue, <- Estate. apply E_funcE; assumption.
      + destruct (evaluation_w_fuel env st1 exp1 fuel) eqn:E1; try (discriminate E).
        destruct p as [v sta]. destruct v; try (discriminate E). destruct env0 as [env_cloG env_cloL]. 
        destruct (evaluation_w_fuel env sta exp2 fuel) eqn:E2; try (discriminate E).
        destruct p as [vala stb].
        apply IHfuel in E1, E2, E. 
        apply E_applyE with env_cloG env_cloL sta stb x exp vala; assumption.
      + destruct (evaluation_w_fuel env st1 exp fuel) eqn:E1; try (discriminate E).
        destruct p as [value0 sta]. injection E as Evalue Estate. apply IHfuel in E1.
        rewrite <- Evalue, <- Estate. assert (H : (Datatypes.length sta) = (Datatypes.length sta)). { reflexivity. }
        apply E_refE; assumption.
      + destruct (evaluation_w_fuel env st1 exp fuel) eqn:E1; try (discriminate E).
        destruct p as [v sta]. destruct v; try (discriminate E).
        destruct (find_nth loc sta) eqn:Efind; try (discriminate E).
        injection E as Evalue Estate. rewrite <- Evalue, <- Estate. apply IHfuel in E1.
        apply E_derefE with loc; assumption.
      + destruct (evaluation_w_fuel env st1 exp1 fuel) eqn:E1; try (discriminate E).
        destruct p as [v sta]. destruct v; try (discriminate E).
        destruct (evaluation_w_fuel env sta exp2 fuel) eqn:E2; try (discriminate E).
        destruct p as [valr stb]. injection E as Evalue Estate. rewrite <- Evalue.
        apply IHfuel in E1, E2.
        apply E_updateE with sta stb loc; assumption.
Qed.

Reserved Notation "C ; St |- p :==> v ; St'"  (at level 80, St at next level, p at next level, v at next level).
Inductive Eval_Prog : environment -> sto -> program -> value -> sto -> Prop :=
    | E_expr : forall env st1 st2 e value,
        (env ; st1 |- e ==> value ; st2) -> env ; st1 |- (LocalDecl e) :==> value ; st2
    | E_decl : forall st st1 st2 envG envL x e p val valp,
        ((envG, envL) ; st |- e ==> val ; st1) ->
        (((x, val) :: envG, envL) ; st1 |- p :==> valp ; st2) ->
        (envG, envL) ; st |- (GlobalDecl (GlobalID x e) p) :==> valp ; st2
where "C ; St |- p :==> v ; St'" := (Eval_Prog C St p v St').

Fixpoint evaluation_w_fuel_program (env : environment) (st : sto) (p : program) (fuel : nat) {struct fuel} : option (value * sto) :=
    match fuel with
    | 0 => None
    | S fuel' =>
        match p with
        | LocalDecl exp => evaluation_w_fuel env st exp fuel'
        | GlobalDecl (GlobalID x exp) p' =>
            let (envG, envL) := env in
            match evaluation_w_fuel (envG, envL) st exp fuel' with
            | Some (val, st1) => (evaluation_w_fuel_program ((x, val) :: envG, envL) st1 p' fuel')
            | None => None
            end
        end
    end.

Theorem Termination_Evaluation_Program :
forall fuel p env st1 st2 value, evaluation_w_fuel_program env st1 p fuel = Some (value, st2) -> env ; st1 |- p :==> value ; st2.
Proof.
    intro fuel.
    induction fuel.
    - intros p env st1 st2 value E. discriminate E.
    - intro p. induction p; intros env st1 st2 value E; simpl in E.
      + destruct gd. destruct env as [envG envL].
        destruct (evaluation_w_fuel (envG, envL) st1 exp fuel) eqn:E1; try (discriminate E).
        destruct p0 as [val sta]. apply IHfuel in E. apply Termination_Evaluation in E1.
        apply E_decl with sta val; assumption.
      + apply Termination_Evaluation in E. apply E_expr; assumption.
Qed.