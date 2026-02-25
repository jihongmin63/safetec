Require Import syntax.
Require Import env.
Require Import primitives.

From Stdlib Require Import String.
From Stdlib Require Import List.
Import ListNotations.

Record subst := {
    subst_EXP : list (id * exp);
    subst_TYP : list (id * typ);
    subst_FUN : list (id * id);
    subst_GRAM : list (id * sym)
}.

Definition concat_subst (s1 s2 : subst) : subst :=
    {|
        subst_EXP := s1.(subst_EXP) ++ s2.(subst_EXP);
        subst_TYP := s1.(subst_TYP) ++ s2.(subst_TYP);
        subst_FUN := s1.(subst_FUN) ++ s2.(subst_FUN);
        subst_GRAM := s1.(subst_GRAM) ++ s2.(subst_GRAM)
    |}.

Record dom := {
    dom_EXP : list id;
    dom_TYP : list id;
    dom_FUN : list id;
    dom_GRAM : list id
}.

Definition concat_dom (d1 d2 : dom) : dom :=
    {|
        dom_EXP := d1.(dom_EXP) ++ d2.(dom_EXP);
        dom_TYP := d1.(dom_TYP) ++ d2.(dom_TYP);
        dom_FUN := d1.(dom_FUN) ++ d2.(dom_FUN);
        dom_GRAM := d1.(dom_GRAM) ++ d2.(dom_GRAM)
    |}.

Definition first_elements {A B : Type} (l : list (A * B)) : list A :=
    List.map (fun (x : A * B) => fst x) l.

Definition dom_subst (s : subst) : dom :=
    {|
        dom_EXP := first_elements s.(subst_EXP);
        dom_TYP := first_elements s.(subst_TYP);
        dom_FUN := first_elements s.(subst_FUN);
        dom_GRAM := first_elements s.(subst_GRAM)
    |}.


Definition bound_param (p : param) : dom :=
    match p with
    | param_EXP x _ =>
      {| dom_EXP := [x]; dom_TYP := []; dom_FUN := []; dom_GRAM := [] |}
    | param_TYP x =>
      {| dom_EXP := []; dom_TYP := [x]; dom_FUN := []; dom_GRAM := [] |}
    | param_FUN x _ _ =>
      {| dom_EXP := []; dom_TYP := []; dom_FUN := [x]; dom_GRAM := [] |}
    | param_GRAM x _ _ =>
      {| dom_EXP := []; dom_TYP := []; dom_FUN := []; dom_GRAM := [x] |}
    end.

Fixpoint bound_params (ps : list param) : dom :=
    match ps with
    | nil =>
        {|
            dom_EXP := []; dom_TYP := []; dom_FUN := []; dom_GRAM := []
        |}
    | cons p ps' =>
        concat_dom (bound_param p) (bound_params ps')
    end.    

Fixpoint subst_aux {A : Type} (s : list (id * A)) (x : id) : option A :=
    match s with
    | nil => None
    | cons (x', y) s' => if String.eqb x' x then Some y else subst_aux s' x
    end.

Definition subst_fun (s : subst) (x : id) : id :=
    match subst_aux s.(subst_FUN) x with
    | Some y => y
    | None => x
    end.

Fixpoint subst_typ (s : subst) (ty : typ) : typ :=
    match ty with
    | typ_plain (plaintyp_op _) => ty
    | typ_plain (plaintyp_TUP ls) => typ_plain (plaintyp_TUP (List.map (fun (l : id * typ) => let (x, t) := l in (x, subst_typ s t)) ls))
    | typ_plain (plaintyp_ITER t it) => typ_plain (plaintyp_ITER (subst_typ s t) (subst_iter s it))
    | typ_VAR x args =>
        match (subst_aux s.(subst_TYP) x), args with
        | Some t, nil => t
        | _, _ => typ_VAR x (List.map (fun arg => subst_arg s arg) args)
        end
    end
with subst_iter (s : subst) (i : iter) : iter :=
    match i with
    | iter_SUP x e =>
      iter_SUP x (subst_exp s e)
    | _ => i
    end
with subst_exp (s : subst) (e : exp) : exp :=
    match e with
    | exp_NUM _ | exp_BOOL _ | exp_TEXT _ => e
    | exp_VAR x =>
        match subst_aux s.(subst_EXP) x with
        | None => e
        | Some e' => e'
        end
    | exp_UN op e => exp_UN op (subst_exp s e)
    | exp_BIN op e1 e2 => exp_BIN op (subst_exp s e1) (subst_exp s e2)
    | exp_CMP op e1 e2 => exp_CMP op (subst_exp s e1) (subst_exp s e2)
    | exp_TUP es => exp_TUP (List.map (fun x => subst_exp s x) es)
    | exp_INJ m e => exp_INJ m (subst_exp s e)
    | exp_OPT option_e =>
        match option_e with
        | Some e => exp_OPT (Some (subst_exp s e))
        | None => exp_OPT None
        end
    | exp_LIST es => exp_LIST (List.map (fun x => subst_exp s x) es)
    | exp_LIFT e => exp_LIFT (subst_exp s e)
    | exp_STR ls =>
        exp_STR (List.map (fun (x : atom * exp) => let (a, e') := x in (a, subst_exp s e')) ls)
    | exp_SEL e n => exp_SEL (subst_exp s e) n
    | exp_LEN e => exp_LEN (subst_exp s e)
    | exp_MEM e1 e2 => exp_MEM (subst_exp s e1) (subst_exp s e2)
    | exp_CAT e1 e2 => exp_CAT (subst_exp s e1) (subst_exp s e2)
    | exp_COMP e1 e2 => exp_COMP (subst_exp s e1) (subst_exp s e2)
    | exp_ACC e p => exp_ACC (subst_exp s e) (subst_path s p)
    | exp_UPD e1 p e2 => exp_UPD (subst_exp s e1) (subst_path s p) (subst_exp s e2)
    | exp_EXT e1 p e2 => exp_EXT (subst_exp s e1) (subst_path s p) (subst_exp s e2)
    | exp_CALL x args => exp_CALL (subst_fun s x) (List.map (fun a => subst_arg s a) args)
    | exp_ITER e i ls => exp_ITER (subst_exp s e) (subst_iter s i) (List.map (fun (l : id * exp) => let (x, e') := l in (x, subst_exp s e')) ls)
    | exp_CVT e nt1 nt2 => exp_CVT (subst_exp s e) nt1 nt2
    | exp_SUB e t1 t2 => exp_SUB (subst_exp s e) t1 t2
    end
with subst_path (s : subst) (p : path) : path :=
    match p with
    | path_ROOT => path_ROOT
    | path_THE p => path_THE (subst_path s p)
    | path_IDX p e => path_IDX (subst_path s p) (subst_exp s e)
    | path_SLICE p1 e p2 => path_SLICE (subst_path s p1) (subst_exp s e) (subst_exp s p2)
    | path_DOT p a => path_DOT (subst_path s p) a
    | path_PROJ p m => path_PROJ (subst_path s p) m
    end
with subst_sym (s : subst) (sy : sym) : sym :=
    match sy with
    | sym_VAR x args =>
        match subst_aux s.(subst_GRAM) x, args with
        | Some g, nil => g
        | Some (sym_VAR y []), _ => sym_VAR y (List.map (fun arg => subst_arg s arg) args)
        | _, _ => sym_VAR x (List.map (fun arg => subst_arg s arg) args)
        end
    | sym_NUM _ | sym_TEXT _ => sy
    | sym_SEQ gs => sym_SEQ (List.map (fun g => subst_sym s g) gs)
    | sym_ALT gs => sym_ALT (List.map (fun g => subst_sym s g) gs)
    | sym_RANGE g1 g2 => sym_RANGE (subst_sym s g1) (subst_sym s g2)
    | sym_ITER g i ls => sym_ITER (subst_sym s g) (subst_iter s i) (List.map (fun (l : id * exp) =>
        let (x, e) := l in (x, subst_exp s e)
      ) ls)
    | sym_ATTR e g => sym_ATTR (subst_exp s e) (subst_sym s g)
    end
with subst_arg (s : subst) (a : arg) : arg :=
    match a with
    | arg_EXP e => arg_EXP (subst_exp s e)
    | arg_TYP t => arg_TYP (subst_typ s t)
    | arg_FUN x => arg_FUN (subst_fun s x)
    | arg_GRAM g => arg_GRAM (subst_sym s g)
    end.

Fixpoint subst_param (s : subst) (p : param) : param :=
    match p with
    | param_EXP x t => param_EXP x (subst_typ s t)
    | param_TYP _ => p
    | param_FUN x ps t => param_FUN x (List.map (fun p => subst_param s p) ps) (subst_typ s t)
    | param_GRAM x ps t => param_GRAM x (List.map (fun p => subst_param s p) ps) (subst_typ s t)
    end.

Definition subst_quant (s : subst) (q : quant) : quant := subst_param s q.

Fixpoint subst_prem (s : subst) (p : prem) : prem :=
    match p with
    | prem_RULE x args e => prem_RULE x (List.map (fun arg => subst_arg s arg) args) (subst_exp s e)
    | prem_IF e => prem_IF (subst_exp s e)
    | prem_ELSE => prem_ELSE
    | prem_LET e1 e2 => prem_LET (subst_exp s e1) (subst_exp s e2)
    | prem_ITER pr i ls => prem_ITER (subst_prem s pr) (subst_iter s i) (List.map (fun (l : id * exp) => let (x, e) := l in (x, subst_exp s e)) ls) 
    end.

Definition subst_deftyp (s : subst) (d : deftyp) : deftyp :=
    match d with
    | deftyp_ALIAS t => deftyp_ALIAS (subst_typ s t)
    | deftyp_STRUCT ls => deftyp_STRUCT (List.map (fun (l : typfield) =>
        let rest := fst l in
        let prs := snd l in
        let at_pair := fst rest in
        let ps := snd rest in
        let a := fst at_pair in
        let t := snd at_pair in
        (a, (subst_typ s t), (List.map (fun p => subst_quant s p) ps), (List.map (fun pr => subst_prem s pr) prs))
      ) ls)
    | deftyp_VARIANT ls => deftyp_VARIANT (List.map (fun (l : typcase) =>
        let rest := fst l in
        let prs := snd l in
        let mt := fst rest in
        let ps := snd rest in
        let m := fst mt in
        let t := snd mt in
        (m, (subst_typ s t), (List.map (fun p => subst_quant s p) ps), (List.map (fun pr => subst_prem s pr) prs))
      ) ls)
    end.

Definition arg_for_param (a : arg) (p : param) : option subst :=
    match a, p with
    | arg_EXP e, param_EXP x t =>
      Some {| subst_EXP := [(x, e)]; subst_TYP := []; subst_FUN := []; subst_GRAM := []|}
    | arg_TYP t, param_TYP x =>
      Some {| subst_EXP := []; subst_TYP := [(x, t)]; subst_FUN := []; subst_GRAM := []|}
    | arg_FUN y, param_FUN x _ _ =>
      Some {| subst_EXP := []; subst_TYP := []; subst_FUN := [(x, y)]; subst_GRAM := []|}
    | arg_GRAM g, param_GRAM x _ _ =>
      Some {| subst_EXP := []; subst_TYP := []; subst_FUN := []; subst_GRAM := [(x, g)]|}
    | _, _ => None
    end.

Fixpoint args_for_params (args : list arg) (params : list param) : option subst :=
    match args, params with
    | nil, nil => Some {| subst_EXP := []; subst_TYP := []; subst_FUN := []; subst_GRAM := []|}
    | cons arg args', cons param params' =>
        match args_for_params args' params' with
        | Some s' =>
            match arg_for_param arg param with
            | Some s => Some (concat_subst s s')
            | None => Some s'
            end
        | None => arg_for_param arg param
        end
    | _, _ => None
    end.

Definition paramarg (p : param) : arg :=
    match p with
    | param_EXP x t => arg_EXP (exp_VAR x)
    | param_TYP x => arg_TYP (typ_VAR x [])
    | param_FUN x ps t => arg_FUN x
    | param_GRAM x ps t => arg_GRAM (sym_VAR x [])
    end.