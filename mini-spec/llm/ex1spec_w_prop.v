From Stdlib Require Import String.
From Stdlib Require Import List.
Import ListNotations.

(* [Definition of the programming language] *)

Definition id := string.

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

(* [Definition of type check and evaluation with fuel] *)

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

Fixpoint evalution_w_fuel (env : environment) (exp : expr) (fuel : nat) : option value :=
    match fuel with
    | 0 => None
    | S fuel' =>
        match exp with
        | NumE n => Some (NumV n)
        | BinE op exp1 exp2 =>
            match (evalution_w_fuel env exp1 fuel'), (evalution_w_fuel env exp2 fuel') with
            | Some (NumV n1), Some (NumV n2) => 
                match op with
                | ADD => Some (NumV (n1 + n2))
                | MUL => Some (NumV (n1 * n2))
                end
            | _, _ => None
            end
        | LetE x exp1 exp2 =>
            match (evalution_w_fuel env exp1 fuel') with
            | Some val => evalution_w_fuel ((x, val) :: env) exp2 fuel'
            | None => None
            end
        | VarE x => find_id x env
        | FuncE x ty exp => Some (CloV x exp env)
        | ApplyE exp1 exp2 =>
            match (evalution_w_fuel env exp1 fuel'), (evalution_w_fuel env exp2 fuel') with
            | Some (CloV x exp env_clo), Some val => (evalution_w_fuel ((x, val) :: env_clo) exp fuel')
            | _, _ => None
            end
        end
    end.

(* [Goals to verify] *)

Theorem Termination_Type_Check :
forall C exp typ, (C |- exp : typ) <-> type_check C exp = Some typ.
Proof.
Admitted.

Theorem Termination_evalution_w_fuel :
forall env exp val n, evalution_w_fuel env exp n = Some val <-> (env |- exp ==> val).
Proof.
Admitted.

Theorem Determinism_Type_Check :
forall C exp typ1 typ2, (C |- exp : typ1) -> (C |- exp : typ2) -> typ1 = typ2.
Proof.
Admitted.

Theorem Determinism_evalution :
forall env exp val1 val2, (env |- exp ==> val1) -> (env |- exp ==> val2) -> val1 = val2.
Proof.
Admitted.