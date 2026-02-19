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
    | T_varE_local : forall CG CL x ty, 
        (find_id x CG = Some ty) -> (CG, CL) |- (VarE x) : ty
    | T_varE_global : forall CG CL x ty, 
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

Reserved Notation "C |- p ; t" (at level 80, p at next level, t at next level).

Inductive Typing_Prog : context -> program -> type -> Prop :=
    | T_P_expr : forall C e ty, (C |- e : ty) -> (C |- (LocalDecl e) ; ty)
    | T_P_decl : forall CG CL x e p ty typ,
        ((CG, CL) |- e : ty) -> ((((x, ty) :: CG), CL) |- p ; typ) -> (CG, CL) |- (GlobalDecl (GlobalID x e) p) ; typ
where "C |- p ; t" := (Typing_Prog C p t).

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
    (env ; sto |- exp ==> value ; sto1) -> (length sto = n) -> env ; sto |- (RefE exp) ==> (LocV n) ; (sto1 ++ [ value ])
  | E_derefE : forall env sto sto1 exp n value,
    (env ; sto |- exp ==> LocV n ; sto1) -> (find_nth n sto1 = Some value) -> env ; sto |- (DerefE exp) ==> value ; sto1
  | E_updateE : forall env sto sto1 sto2 sto3 el er n valr,
    (env ; sto |- el ==> (LocV n); sto1) -> (env ; sto1 |- er ==> valr ; sto2) -> (change_nth n valr sto2 = sto3) -> env ; sto |- (UpdateE el er) ==> valr ; sto3
where "C ; St |- e ==> v ; St'" := (Eval C St e v St').

Reserved Notation "C ; St |- p :==> v ; St'"  (at level 80, St at next level, p at next level, v at next level).
Inductive Eval_Prog : environment -> sto -> program -> value -> sto -> Prop :=
    | E_decl : forall st st1 st2 envG envL x e p val valp,
        ((envG, envL) ; st |- e ==> val ; st1) ->
        (((x, val) :: envG, envL) ; st1 |- p :==> valp ; st2) ->
        (envG, envL) ; st |- (GlobalDecl (GlobalID x e) p) :==> valp ; st2
where "C ; St |- p :==> v ; St'" := (Eval_Prog C St p v St').