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

(* [Goals to verify] *)

Theorem Termination_Type_Check :
(* FILL this BLANK! *).
Proof.
Admitted.

Theorem Termination_evalution_w_fuel :
(* FILL this BLANK! *).
Proof.
Admitted.

Theorem Determinism_Type_Check :
(* FILL this BLANK! *).
Proof.
Admitted.

Theorem Determinism_evalution :
(* FILL this BLANK! *).
Proof.
Admitted.