Require Import syntax.
Require Import env.
Require Import primitives.
Require Import subst.

From Stdlib Require Import List.
From Stdlib Require Import String.
Import ListNotations.

Fixpoint disjoint {X : Type} (xs : list X) : Prop :=
    match xs with
    | nil => True
    | cons x xs_rest =>
        (In x xs_rest -> False) /\ (disjoint xs_rest)
    end.

Definition transpose_aux (X : Type) (xss : list (list X)) : option (list X * list (list X)) :=
    match xss with
    | nil => Some (nil, nil)
    | first_row :: rows_rest =>
        match first_row with
        | nil => None
        | h :: t =>
            match (fix help (rs : list (list X)) :=
                match rs with
                | nil => Some (nil, nil)
                | r :: rs_rest =>
                    match r with
                    | nil => None
                    | h' :: t' => 
                        match help rs_rest with
                        | Some (hs, ts) => Some (h' :: hs, t' :: ts)
                        | None => None
                        end
                    end
                end) rows_rest with
            | Some (hs, ts) => Some (h :: hs, t :: ts)
            | None => None
            end
        end
    end.

Fixpoint transpose_acc (X : Type) (n : nat) (xss : list (list X)) : option (list (list X)) :=
    match n with
    | O => Some nil
    | Datatypes.S n' =>
        match transpose_aux X xss with
        | None => None
        | Some (heads, nexts) =>
            match transpose_acc X n' nexts with
            | None => None
            | Some rest => Some (heads :: rest)
            end
        end
    end.

Definition transpose (X : Type) (xss : list (list X)) : option (list (list X)) :=
    match xss with
    | nil => Some nil
    | col1 :: _ => transpose_acc X (List.length col1) xss
    end.

Fixpoint list_element {X : Type} (f : nat -> X) (len : nat) : list X :=
    match len with
    | O => [f O]
    | Datatypes.S len' => (list_element f len') ++ [f len]
    end.

Fixpoint Step_exp_SUB_TUP_aux (es : list exp) (tups : list (id * typ)) : option (list (id * exp)) :=
    match es, tups with
    | [], [] => Some nil
    | e :: es_rest, tup :: tups_rest =>
        match Step_exp_SUB_TUP_aux es_rest tups_rest with
        | None => None
        | Some ls =>
            let (x, _) := tup in
            Some ((x, e) :: ls)
        end
    | _, _ => None
    end.

Fixpoint find_nth {A : Type} (n : nat) (l : list A) : option A :=
    match n, l with
    | 1, head :: tail => Some head
    | Datatypes.S m, head :: tail => find_nth m tail
    | _, _ => None
    end.

Fixpoint change_nth {A : Type} (n : nat) (val : A) (l : list A) : list A :=
    match l with
    | head :: tail =>
        match n with
        | 0 | 1 => val :: tail
        | Datatypes.S m => head :: (change_nth m val tail)
        end
    | [] => []
    end.

Definition env_EXP_one (x : id) (t : typ) : E := env.env_EXP_generator [(x, t)].

Inductive Expand_typ : S -> typ -> deftyp -> Prop :=
    | Expand_typ_plain : forall sub (t : plaintyp), Expand_typ sub (typ_plain t) (deftyp_ALIAS (typ_plain t))
    | Expand_typ_alias : forall sub x args t dt,
        (Expand_typ sub (typ_VAR x args) (deftyp_ALIAS t)) ->
        (Expand_typ sub t dt) ->
        Expand_typ sub (typ_VAR x args) dt
    | Expand_typ_step : forall sub x args ps insts qs args' s dt,
        (In (x, (ps, insts)) sub.(S_TYP)) ->
        (In (INST qs args' dt) insts) ->
        (Match_args sub args qs args' s) ->
        Expand_typ sub (typ_VAR x args) (subst_deftyp s dt)
with Eq_typ : S -> typ -> typ -> Prop :=
    | Eq_typ_prop : forall sub t1 t2 t1' t2',
        (Reduce_typ sub t1 t1') ->
        (Reduce_typ sub t2 t2') ->
        (t1' = t2') ->
        Eq_typ sub t1 t2
with Reduce_typ : S -> typ -> typ -> Prop :=
    | Reduce_typ_normal : forall sub t, Reduce_typ sub t t
    | Reduce_typ_step : forall sub t t' t'',
        (Step_typ sub t t') ->
        (Reduce_typ sub t' t'') ->
        Reduce_typ sub t t''
with Step_typ : S -> typ -> typ -> Prop :=
    | Step_typ_VAR_ctx : forall sub x args argn argn' n,
        (find_nth n args = Some argn) ->
        (Step_arg sub argn argn') ->
        Step_typ sub (typ_VAR x args) (typ_VAR x (change_nth n argn' args))
    | Step_typ_VAR_apply : forall sub x args t,
        (Expand_typ sub (typ_VAR x args) (deftyp_ALIAS t)) ->
        Step_typ sub (typ_VAR x args) t
    | Step_typ_TUP_ctx : forall sub tups xn tn tn' n,
        (find_nth n tups = Some (xn, tn)) ->
        (Step_typ sub tn tn') ->
        (Step_typ sub (typ_plain (plaintyp_TUP tups)) (typ_plain (plaintyp_TUP (change_nth n (xn, tn') tups))))
    | Step_typ_ITER_ctx : forall sub t it t',
        (Step_typ sub t t') ->
        (Step_typ sub (typ_plain (plaintyp_ITER t it)) (typ_plain (plaintyp_ITER t' it)))
with Reduce_exp : S -> exp -> exp -> Prop :=
    | Reduce_exp_normal : forall sub e, Reduce_exp sub e e
    | Reduce_exp_step : forall sub e e' e'',
        (Step_exp sub e e') ->
        (Reduce_exp sub e' e'') ->
        Reduce_exp sub e e''
with Step_exp : S -> exp -> exp -> Prop :=
    | Step_exp_UN_ctx : forall sub op e e',
        (Step_exp sub e e') ->
        Step_exp sub (exp_UN op e) (exp_UN op e')
    | Step_exp_UN_BOOOL : forall sub (op : boolunop) b, Step_exp sub (exp_UN op (exp_BOOL b)) (exp_BOOL (boolun op b))
    | Step_exp_UN_NUM : forall sub (op : numunop) (n : num), Step_exp sub (exp_UN op (exp_NUM n)) (exp_NUM (numun op n))
    | Step_exp_BIN_ctx1 : forall sub op e1 e2 e1',
        (Step_exp sub e1 e1') ->
        Step_exp sub (exp_BIN op e1 e2) (exp_BIN op e1' e2)
    | Step_exp_BIN_ctx2 : forall sub op e1 e2 e2',
        (Step_exp sub e2 e2') ->
        Step_exp sub (exp_BIN op e1 e2) (exp_BIN op e1 e2')
    | Step_exp_BIN_BOOL : forall sub (op : boolbinop) b1 b2, Step_exp sub (exp_BIN op (exp_BOOL b1) (exp_BOOL b2)) (exp_BOOL (boolbin op b1 b2))
    | Step_exp_BIN_NUM : forall sub (op : numbinop) (n1 n2 n : num), 
        (numbin op n1 n2 = Some n) ->
        Step_exp sub (exp_BIN op (exp_NUM n1) (exp_NUM n2)) (exp_NUM n)
    | Step_exp_CMP_ctx1 : forall sub op e1 e2 e1',
        (Step_exp sub e1 e1') ->
        Step_exp sub (exp_CMP op e1 e2) (exp_CMP op e1' e2)
    | Step_exp_CMP_ctx2 : forall sub op e1 e2 e2',
        (Step_exp sub e2 e2') ->
        Step_exp sub (exp_CMP op e1 e2) (exp_CMP op e1 e2')
    | Step_exp_CMP_EQ_true : forall sub e1 e2,
        (e1 = e2) ->
        Step_exp sub (exp_CMP (cmpop_poly EQ) e1 e2) (exp_BOOL true)
    | Step_exp_CMP_EQ_false : forall sub e1 e2,
        (e1 = e2 -> False) ->
        Step_exp sub (exp_CMP (cmpop_poly EQ) e1 e2) (exp_BOOL false)
    | Step_exp_CMP_NE_true : forall sub e1 e2,
        (e1 = e2 -> False) ->
        Step_exp sub (exp_CMP (cmpop_poly NE) e1 e2) (exp_BOOL true)
    | Step_exp_CMP_NE_false : forall sub e1 e2,
        (e1 = e2) ->
        Step_exp sub (exp_CMP (cmpop_poly NE) e1 e2) (exp_BOOL false)
    | Step_exp_CMP_NUM : forall sub (op : numcmpop) (n1 n2 : num) (b : bool),
        (numcmp op n1 n2 = Some b) ->
        Step_exp sub (exp_CMP (cmpop_num op) (exp_NUM n1) (exp_NUM n2)) (exp_BOOL b)
    | Step_exp_OPT_ctx : forall sub e e',
        (Step_exp sub e e') ->
        Step_exp sub (exp_OPT (Some e)) (exp_OPT (Some e'))
    | Step_exp_LIST_ctx : forall sub es n e_n e_n',
        (find_nth n es = Some e_n) ->
        (Step_exp sub e_n e_n') ->
        Step_exp sub (exp_LIST es) (exp_LIST (change_nth n e_n' es))
    | Step_exp_TUP_ctx : forall sub es n e_n e_n',
        (find_nth n es = Some e_n) ->
        (Step_exp sub e_n e_n') ->
        Step_exp sub (exp_TUP es) (exp_TUP (change_nth n e_n' es))
    | Step_exp_STR_ctx : forall sub aes n an e_n e_n',
        (find_nth n aes = Some (an, e_n)) ->
        (Step_exp sub e_n e_n') ->
        Step_exp sub (exp_STR aes) (exp_STR (change_nth n (an, e_n') aes))
    | Step_exp_INJ_ctx : forall sub m e e',
        (Step_exp sub e e') ->
        Step_exp sub (exp_INJ m e) (exp_INJ m e')
    | Step_exp_LIFT_ctx : forall sub e e',
        (Step_exp sub e e') ->
        Step_exp sub (exp_LIFT e) (exp_LIFT e')
    | Step_exp_LIFT_none : forall sub, Step_exp sub (exp_LIFT (exp_OPT None)) (exp_LIST [])
    | Step_exp_LIFT_some : forall sub e, Step_exp sub (exp_LIFT (exp_OPT (Some e))) (exp_LIST [e])
    | Step_exp_SEL_ctx : forall sub e n e',
        (Step_exp sub e e') ->
        Step_exp sub (exp_SEL e n) (exp_SEL e' n)
    | Step_exp_SEL_tup : forall sub es n e_n,
        (find_nth n es = Some e_n) ->
        Step_exp sub (exp_SEL (exp_TUP es) n) e_n
    | Step_exp_LEN_ctx : forall sub e e',
        (Step_exp sub e e') ->
        Step_exp sub (exp_LEN e) (exp_LEN e')
    | Step_exp_LEN_list : forall sub es,
        Step_exp sub (exp_LEN (exp_LIST es)) (exp_NUM (NAT (List.length es)))
    | Step_exp_MEM_ctx1 : forall sub e1 e2 e1',
        (Step_exp sub e1 e1') ->
        Step_exp sub (exp_MEM e1 e2) (exp_MEM e1' e2)
    | Step_exp_MEM_ctx2 : forall sub e1 e2 e2',
        (Step_exp sub e2 e2') ->
        Step_exp sub (exp_MEM e1 e2) (exp_MEM e1 e2')
    | Step_exp_MEM_OPT_true : forall sub e1 e2,
        (e1 = e2) -> 
        Step_exp sub (exp_MEM e1 (exp_OPT (Some e2))) (exp_BOOL true)
    | Step_exp_MEM_OPT_false_Some : forall sub e1 e2,
        (e1 = e2 -> False) ->
        Step_exp sub (exp_MEM e1 (exp_OPT (Some e2))) (exp_BOOL false)
    | Step_exp_MEM_LIST_true : forall sub e1 es n,
        (find_nth n es = Some e1) ->
        Step_exp sub (exp_MEM e1 (exp_LIST es)) (exp_BOOL true)
    | Step_exp_MEM_LIST_false : forall sub e1 es,
        (forall e, In e es -> (e1 = e -> False)) ->
        Step_exp sub (exp_MEM e1 (exp_LIST es)) (exp_BOOL false)
    | Step_exp_CAT_ctx1 : forall sub e1 e2 e1',
        (Step_exp sub e1 e1') ->
        Step_exp sub (exp_CAT e1 e2) (exp_CAT e1' e2)
    | Step_exp_CAT_ctx2 : forall sub e1 e2 e2',
        (Step_exp sub e2 e2') ->
        Step_exp sub (exp_CAT e1 e2) (exp_CAT e1 e2')
    | Step_exp_CAT_opt1 : forall sub e1, Step_exp sub (exp_CAT (exp_OPT (Some e1)) (exp_OPT None)) (exp_OPT (Some e1))
    | Step_exp_CAT_opt2 : forall sub e2, Step_exp sub (exp_CAT (exp_OPT None) (exp_OPT (Some e2))) (exp_OPT (Some e2))
    | Step_exp_CAT_list : forall sub e1s e2s, Step_exp sub (exp_CAT (exp_LIST e1s) (exp_LIST e2s)) (exp_LIST (e1s ++ e2s))
    | Step_exp_CAT_str : forall sub args es1 es2, Step_exp sub (exp_CAT (exp_STR (combine args es1)) (exp_STR (combine args es2))) (exp_STR (combine args (map (fun e12 => exp_CAT (fst e12) (snd e12)) (combine es1 es2))))
    | Step_exp_ACC_ctx1 : forall sub e p e',
        (Step_exp sub e e') ->
        Step_exp sub (exp_ACC e p) (exp_ACC e' p)
    | Step_exp_ACC_ctx2 : forall sub e p p',
        (Step_path sub p p') ->
        Step_exp sub (exp_ACC e p) (exp_ACC e p')
    | Step_exp_ACC_ROOT : forall sub e, Step_exp sub (exp_ACC e path_ROOT) e
    | Step_exp_ACC_IDX : forall sub e p n es e_n,
        (Step_exp sub (exp_ACC e p) (exp_LIST es)) ->
        (find_nth n es = Some e_n) ->
        Step_exp sub (exp_ACC e (path_IDX p (exp_NUM (NAT (n - 1))))) e_n
    | Step_exp_ACC_SLICE : forall sub e p n m es1 es2 es3,
        (Step_exp sub (exp_ACC e p) (exp_LIST (es1 ++ es2 ++ es3))) ->
        (List.length es1 = n) ->
        (List.length es2 = m) ->
        Step_exp sub (exp_ACC e (path_SLICE p (NAT n) (NAT m))) (exp_LIST es2)
    | Step_exp_ACC_DOT : forall sub e p a aes n e_n,
        (Step_exp sub (exp_ACC e p) (exp_STR aes)) ->
        (find_nth n aes = Some (a, e_n)) ->
        Step_exp sub (exp_ACC e (path_DOT p a)) e_n
    | Step_exp_ACC_PROJ : forall sub e p m e',
        (Step_exp sub (exp_ACC e p) (exp_INJ m e')) ->
        Step_exp sub (exp_ACC e (path_PROJ p m)) e'
    | Step_exp_UPD_ctx1 : forall sub e1 p e2 e1',
        (Step_exp sub e1 e1') ->
        Step_exp sub (exp_UPD e1 p e2) (exp_UPD e1' p e2)
    | Step_exp_UPD_ctx2 : forall sub e1 p e2 p',
        (Step_path sub p p') ->
        Step_exp sub (exp_UPD e1 p e2) (exp_UPD e1 p' e2)
    | Step_exp_UPD_ctx3 : forall sub e1 p e2 e2',
        (Step_exp sub e2 e2') ->
        Step_exp sub (exp_UPD e1 p e2) (exp_UPD e1 p e2')
    | Step_exp_UPD_ROOT : forall sub e1 e2, Step_exp sub (exp_UPD e1 path_ROOT e2) e2
    | Step_exp_UPD_THE : forall sub e1 p e2 e',
        (Step_exp sub (exp_ACC e1 p) (exp_OPT (Some e'))) ->
        Step_exp sub (exp_UPD e1 (path_THE p) e2) (exp_UPD e1 p (exp_OPT (Some e2)))
    | Step_exp_UPD_IDX : forall sub e1 p n e2 es,
        (Step_exp sub (exp_ACC e1 p) (exp_LIST es)) ->
        (1 <= n <= List.length es) ->
        Step_exp sub (exp_UPD e1 (path_IDX p (exp_NUM (NAT (n - 1)))) e2) (exp_UPD e1 p (exp_LIST (change_nth n e2 es)))
    | Step_exp_UPD_SLICE : forall sub e1 p n m es1 es2 es3 es2',
        (Step_exp sub (exp_ACC e1 p)) (exp_LIST (es1 ++ es2 ++ es3)) ->
        (List.length es1 = n) ->
        (List.length es2 = m) ->
        Step_exp sub (exp_UPD e1 (path_SLICE p (NAT n) (NAT m)) (exp_LIST es2')) (exp_UPD e1 p (exp_LIST (es1 ++ es2' ++ es3)))
    | Step_exp_UPD_DOT : forall sub e1 p a e2 aes n e',
        (Step_exp sub (exp_ACC e1 p) (exp_STR aes)) ->
        (find_nth n aes = Some (a, e')) ->
        Step_exp sub (exp_UPD e1 (path_DOT p a) e2) (exp_UPD e1 p (exp_STR (change_nth n (a, e2) aes)))
    | Step_exp_UPD_PROJ : forall sub e1 p m e2 e',
        (Step_exp sub (exp_ACC e1 p) (exp_INJ m e')) ->
        Step_exp sub (exp_UPD e1 (path_PROJ p m) e2) (exp_UPD e1 p (exp_INJ m e2))
    | Step_exp_EXT : forall sub e1 p e2, Step_exp sub (exp_EXT e1 p e2) (exp_UPD e1 p (exp_CAT (exp_ACC e1 p) e2))
    | Step_exp_ITER_ctx1 : forall sub e it eps e',
        (Step_exp sub e e') ->
        Step_exp sub (exp_ITER e it eps) (exp_ITER e' it eps)
    | Step_exp_ITER_ctx2 : forall sub e it eps it',
        (Step_iter sub it it') ->
        Step_exp sub (exp_ITER e it eps) (exp_ITER e it' eps)
    | Step_exp_ITER_ctx3 : forall sub e it eps n xn e_n e_n',
        (find_nth n eps = Some (xn, e_n)) ->
        (Step_exp sub e_n e_n') ->
        Step_exp sub (exp_ITER e it eps) (exp_ITER e it (change_nth n (xn, e_n') eps))
    | Step_exp_ITER_QUEST_Some : forall sub e xs es, Step_exp sub (exp_ITER e iter_QUEST (combine xs (map (fun e' => exp_OPT (Some e')) es))) (exp_OPT (Some (subst_exp (subst_EXP_generator (combine xs es)) e)))
    | Step_exp_ITER_QUEST_None : forall sub e xs, Step_exp sub (exp_ITER e iter_QUEST (map (fun x => (x, exp_OPT None)) xs)) (exp_OPT None)
    | Step_exp_ITER_PLUS : forall sub e es1_head es1_tail ess x1 xs, Step_exp sub (exp_ITER e iter_PLUS ((x1, exp_LIST (es1_head :: es1_tail)) :: (combine xs (map (fun es => exp_LIST es) ess)))) (exp_ITER e iter_STAR ((x1, exp_LIST (es1_head :: es1_tail)) :: (combine xs (map (fun es => exp_LIST es) ess))))
    | Step_exp_ITER_STAR : forall sub e x xs es ess n,
        (List.length es = n) ->
        Step_exp sub (exp_ITER e iter_STAR ((x, exp_LIST es) :: (combine xs (map (fun es' => exp_LIST es') ess)))) (exp_ITER e (iter_SUP None (NAT n)) ((x, exp_LIST es) :: (combine xs (map (fun es' => exp_LIST es') ess))))
    | Step_exp_ITER_SUP_eps : forall sub e en xs ess y, Step_exp sub (exp_ITER e (iter_SUP None en) (combine xs (map (fun es' => exp_LIST es') ess))) (exp_ITER e (iter_SUP (Some y) en) (combine xs (map (fun es' => exp_LIST es') ess)))
    | Step_exp_ITER_SUP : forall sub e y n xs ess ess_transposed,
        (forall es, In es ess -> List.length es = n) ->
        (transpose exp ess = Some ess_transposed) ->
        Step_exp sub
          (exp_ITER e (iter_SUP (Some y) (NAT n)) (combine xs (map (fun es => exp_LIST es) ess)))
          (exp_LIST (map (fun esi => subst_exp (subst_EXP_generator ((combine xs (fst esi)) ++ [(y, exp_NUM (NAT (snd esi)))])) e) (combine ess_transposed (list_element (fun num => num) n))))
    | Step_exp_CALL_ctx : forall sub x args n argn argn',
        (find_nth n args = Some argn) ->
        (Step_arg sub argn argn') ->
        Step_exp sub (exp_CALL x args) (exp_CALL x (change_nth n argn' args))
    | Step_exp_CALL_apply : forall sub x args ps t clauses qs args' e prs s,
        (In (x, (ps, t, clauses)) sub.(S_FUN)) ->
        (In (CLAUSE qs args' e prs) clauses) ->
        (Match_args sub args qs args' s) ->
        (Reduce_prems sub (map (fun pr => subst_prem s pr) prs) []) ->
        Step_exp sub (exp_CALL x args) (subst_exp s e)
    | Step_exp_CVT_ctx : forall sub e nt1 nt2 e',
        (Step_exp sub e e') ->
        Step_exp sub (exp_CVT e nt1 nt2) (exp_CVT e' nt1 nt2)
    | Step_exp_CVT_NUM : forall sub (n : num) nt1 nt2 (n' : num),
        (numcvt nt2 n = Some n') ->
        Step_exp sub (exp_CVT (exp_NUM n) nt1 nt2) (exp_NUM n')
    | Step_exp_SUB_ctx1 : forall sub e t1 t2 e',
        (Step_exp sub e e') ->
        Step_exp sub (exp_SUB e t1 t2) (exp_SUB e' t1 t2)
    | Step_exp_SUB_ctx2 : forall sub e t1 t2 t1',
        (Step_typ sub t1 t1') ->
        Step_exp sub (exp_SUB e t1 t2) (exp_SUB e t1' t2)
    | Step_exp_SUB_ctx3 : forall sub e t1 t2 t2',
        (Step_typ sub t2 t2') ->
        Step_exp sub (exp_SUB e t1 t2) (exp_SUB e t1 t2')
    | Step_exp_SUB_SUB : forall sub e' t1' t2' t1 t2, Step_exp sub (exp_SUB (exp_SUB e' t1' t2') t1 t2) (exp_SUB e' t1' t2)
    | Step_exp_SUB_TUB : forall sub n es tups1 tups2 s1 s2,
        (List.length es = n) ->
        (List.length tups1 = n) ->
        (List.length tups2 = n) ->
        (Step_exp_SUB_TUP_aux es tups1 = Some s1) ->
        (Step_exp_SUB_TUP_aux es tups2 = Some s2) ->
        Step_exp sub (exp_SUB (exp_TUP es) (typ_plain (plaintyp_TUP tups1)) (typ_plain (plaintyp_TUP tups2))) (exp_TUP (map (fun (x : ((id * typ) * (id * typ)) * exp) =>
            exp_SUB (snd x) (subst_typ (subst.subst_EXP_generator s1) (snd (fst (fst x)))) (subst_typ (subst.subst_EXP_generator s2) (snd (snd (fst x))))
        ) (combine (combine tups1 tups2) es)))
    | Step_exp_SUB_OPT_Some : forall sub e t1 t2, Step_exp sub (exp_SUB (exp_OPT (Some e)) (typ_plain (plaintyp_ITER t1 iter_QUEST)) (typ_plain (plaintyp_ITER t2 iter_QUEST))) (exp_OPT (Some (exp_SUB e t1 t2)))
    | Step_exp_SUB_OPT_None : forall sub t1 t2, Step_exp sub (exp_SUB (exp_OPT None) (typ_plain (plaintyp_ITER t1 iter_QUEST)) (typ_plain (plaintyp_ITER t2 iter_QUEST))) (exp_OPT None)
    | Step_exp_SUB_LIST : forall sub es t1 t2, Step_exp sub (exp_SUB (exp_LIST es) (typ_plain (plaintyp_ITER t1 iter_STAR)) (typ_plain (plaintyp_ITER t2 iter_STAR))) (exp_LIST (map (fun e => exp_SUB e t1 t2) es))
    | Step_exp_SUB_STR : forall sub efs x1 args1 x2 args2 ats es ts1 ts2 q1ss q2ss pr1ss pr2ss tfs1 ,
        (Expand_typ sub (typ_VAR x1 args1) (deftyp_STRUCT tfs1)) ->
        (Expand_typ sub (typ_VAR x2 args2) (deftyp_STRUCT (combine (combine (combine ats ts2) q2ss) pr2ss))) ->
        (forall x, In x (combine (combine (combine ats ts1) q1ss) pr1ss) -> In x tfs1) ->
        (forall ate, In ate (combine ats es) -> In ate efs) ->
        Step_exp sub (exp_SUB (exp_STR efs) (typ_VAR x1 args1) (typ_VAR x2 args2)) (exp_STR (combine ats (map (fun ett => exp_SUB (fst ett) (fst (snd ett)) (snd (snd ett))) (combine es (combine ts1 ts2)))))
    | Step_exp_SUB_CASE : forall sub op e x1 args1 x2 args2 t1 t2 tcs1 tcs2 qs1 qs2 prs1 prs2,
        (Expand_typ sub (typ_VAR x1 args1) (deftyp_VARIANT tcs1)) ->
        (Expand_typ sub (typ_VAR x2 args2) (deftyp_VARIANT tcs2)) ->
        (In (op, t1, qs1, prs1) tcs1) ->
        (In (op, t2, qs2, prs2) tcs2) ->
        Step_exp sub (exp_SUB (exp_INJ op e) (typ_VAR x1 args1) (typ_VAR x2 args2)) (exp_INJ op (exp_SUB e t1 t2))
with Step_path : S -> path -> path -> Prop :=
    | Step_path_refl : forall sub p, Step_path sub p p
with Step_iter : S -> iter -> iter -> Prop :=
    | Step_iter_refl : forall sub it, Step_iter sub it it
with Step_exppull : S -> exppull -> exppull -> Prop :=
    | Step_exppull_refl : forall sub ep, Step_exppull sub ep ep
with Eq_exp : S -> exp -> exp -> Prop :=
    | Eq_exp_prop : forall sub e1 e2 e1' e2',
        (Reduce_exp sub e1 e1') ->
        (Reduce_exp sub e2 e2') ->
        (e1' = e2') ->
        Eq_exp sub e1 e2
with Reduce_arg : S -> arg -> arg -> Prop :=
    | Reduce_arg_normal : forall sub a, Reduce_arg sub a a
    | Reduce_arg_step : forall sub a a' a'',
        (Step_arg sub a a') ->
        (Reduce_arg sub a' a'') ->
        Reduce_arg sub a a''
with Step_arg : S -> arg -> arg -> Prop :=
    | Step_arg_EXP_ctx : forall sub e e',
        (Step_exp sub e e') ->
        Step_arg sub (arg_EXP e) (arg_EXP e')
    | Step_arg_TYP_ctx : forall sub t t',
        (Step_typ sub t t') ->
        Step_arg sub (arg_TYP t) (arg_TYP t')
with Eq_arg : S -> arg -> arg -> Prop :=
    | Eq_arg_prop : forall sub a1 a2 a1' a2',
        (Reduce_arg sub a1 a1') ->
        (Reduce_arg sub a2 a2') ->
        (a1' = a2') ->
        Eq_arg sub a1 a2
with Match_args : S -> list arg -> list quant -> list arg -> subst -> Prop :=
    | Match_args_prop : forall sub args qs args' s,
        (Ok_subst (storenv sub) s qs) ->
        (args = (map (fun arg' => subst_arg s arg') args')) ->
        Match_args sub args qs args' s
with Reduce_prems : S -> list prem -> list prem -> Prop :=
    | Reduce_prems_normal : forall sub prs, Reduce_prems sub prs prs
    | Reduce_prems_step : forall sub prs prs' prs'',
        (Step_prems sub prs prs') ->
        (Reduce_prems sub prs' prs'') ->
        Reduce_prems sub prs prs''
with Step_prems : S -> list prem -> list prem -> Prop :=
    | Step_prems_ctx : forall sub pr1 prs pr1s',
        (Step_prems sub [pr1] pr1s') ->
        Step_prems sub (pr1 :: prs) (pr1s' ++ prs)
    | Step_prems_IF_ctx : forall sub e e',
        (Step_exp sub e e') ->
        Step_prems sub [prem_IF e] [prem_IF e']
    | Step_prems_IF_true : forall sub, Step_prems sub [prem_IF (exp_BOOL true)] []
    | Step_prems_ELSE : forall sub, Step_prems sub [prem_ELSE] []
    | Step_prems_LET_ctx : forall sub e1 e2 e2',
        (Step_exp sub e2 e2') ->
        Step_prems sub [prem_LET e1 e2] [prem_LET e1 e2']
    | Step_prems_LET : forall sub e1 e2,
        (Eq_exp sub e1 e2) ->
        Step_prems sub [prem_LET e1 e2] []
    | Step_prems_ITER_ctx1 : forall sub pr it eps pr',
        (Step_prems sub [pr] [pr']) ->
        Step_prems sub [prem_ITER pr it eps] [prem_ITER pr' it eps]
    | Step_prems_ITER_ctx2 : forall sub pr it eps it',
        (Step_iter sub it it') ->
        Step_prems sub [prem_ITER pr it eps] [prem_ITER pr it' eps]
    | Step_prems_ITER_ctx3 : forall sub pr it eps n ep_n ep_n',
        (find_nth n eps = Some ep_n) ->
        (Step_exppull sub ep_n ep_n') ->
        Step_prems sub [prem_ITER pr it eps] [prem_ITER pr it (change_nth n ep_n' eps)]
    | Step_prems_ITER_QUEST_ALL : forall sub pr xs es, Step_prems sub [prem_ITER pr iter_QUEST (combine xs (map (fun e => exp_OPT (Some e)) es))] [subst_prem (subst_EXP_generator (combine xs es)) pr]
    | Step_prems_ITER_QUEST_NONE : forall sub pr xs, Step_prems sub [prem_ITER pr iter_QUEST (map (fun x => (x, exp_OPT None)) xs)] nil
    | Step_prems_ITER_PLUS : forall sub pr x xs e1_head e1_tail ess, Step_prems sub [prem_ITER pr iter_PLUS ((x, exp_LIST (e1_head :: e1_tail)) :: (combine xs (map (fun es => exp_LIST es) ess)))] [prem_ITER pr iter_STAR ((x, exp_LIST (e1_head :: e1_tail)) :: (combine xs (map (fun es => exp_LIST es) ess)))]
    | Step_prems_ITER_STAR : forall sub pr x es xs ess n,
        (List.length es = n) ->
        Step_prems sub [prem_ITER pr iter_STAR ((x, exp_LIST es) :: (combine xs (map (fun es' => exp_LIST es') ess)))] [prem_ITER pr (iter_SUP None (NAT n)) ((x, exp_LIST es) :: (combine xs (map (fun es' => exp_LIST es') ess)))]
    | Step_prems_SUP_eps : forall sub pr en xs ess y, Step_prems sub [prem_ITER pr (iter_SUP None en) (combine xs (map (fun es => exp_LIST es) ess))] [prem_ITER pr (iter_SUP (Some y) en) (combine xs (map (fun es => exp_LIST es) ess))]
    | Step_prems_SUP : forall sub pr y n xs ess ess_transposed,
        (forall es, In es ess -> List.length es = n) ->
        (transpose exp ess = Some ess_transposed) ->
        Step_prems sub [prem_ITER pr (iter_SUP (Some y) (NAT n)) (combine xs (map (fun es => exp_LIST es) ess))] (map (fun xi => subst_prem (subst_EXP_generator ((combine xs (nth (snd xi) ess_transposed [])) ++ [(y, exp_NUM (NAT (snd xi)))])) pr) (combine xs (list_element (fun idx => idx) n)))
with Eq_prems : S -> list prem -> list prem -> Prop :=
    | Eq_prems_refl : forall sub prs, Eq_prems sub prs prs
with Composable_typ : E -> typ -> Prop :=
    | Composable_typ_ITER : forall (e : E) t t' it,
        (Expand_typ e.(E_S) t (deftyp_ALIAS (typ_plain (plaintyp_ITER t' it)))) ->
        Composable_typ e t
    | Composable_typ_STRUCT : forall (e : E) t (sts : list typfield),
        (Expand_typ e.(E_S) t (deftyp_STRUCT sts)) ->
        (forall x, In x sts -> Composable_typ e (snd (fst (fst x)))) ->
        Composable_typ e t
with Sub_numtyp : numtyp -> numtyp -> Prop :=
    | Sub_numtyp_nat : Sub_numtyp numtyp_NAT numtyp_INT
    | Sub_numtyp_int : Sub_numtyp numtyp_INT numtyp_RAT
    (*| Sub_numtyp_rat : Sub_numtyp numtyp_RAT numtyp_REAL*)
    | Sub_numtyp_refl : forall nt, Sub_numtyp nt nt
    | Sub_numtyp_trans : forall nt1 nt' nt2,   
        (Sub_numtyp nt1 nt') ->
        (Sub_numtyp nt' nt2) ->
        Sub_numtyp nt1 nt2
with Sub_typ : E -> typ -> typ -> Prop :=
    | Sub_typ_tup : forall (e : E) x1 t1 tups1 x2 t2 tups2,
        (Sub_typ e t1 t2) ->
        (Sub_typ (concat_E e (env_EXP_one x1 t1)) (typ_plain (plaintyp_TUP tups1)) (subst_typ (subst.subst_TYP_generator [(x2, typ_VAR x1 nil)]) (typ_plain (plaintyp_TUP tups2)))) ->
        Sub_typ e (typ_plain (plaintyp_TUP ((x1, t1) :: tups1))) (typ_plain (plaintyp_TUP ((x2, t2) :: tups2)))
    | Sub_typ_struct : forall (e : E) t1 t2 args t1as t2as qss prss tf1s tf2s,
        (Expand_typ e.(E_S) t1 (deftyp_STRUCT tf1s)) ->
        (Expand_typ e.(E_S) t2 (deftyp_STRUCT tf2s)) ->
        (tf2s = (combine (combine (combine args t2as) qss) prss)) ->
        (forall tf1, In tf1 (combine (combine (combine args t1as) qss) prss) -> In tf1 tf1s) ->
        (forall t12, In t12 (combine t1as t2as) -> Sub_typ e (fst t12) (snd t12)) ->
        Sub_typ e t1 t2
    | Sub_typ_variant: forall (e : E) t1 t2 tc1s tc2s ms t1as t2as qss prss,
        (Expand_typ e.(E_S) t1 (deftyp_VARIANT tc1s)) ->
        (Expand_typ e.(E_S) t2 (deftyp_VARIANT tc2s)) ->
        (tc1s = combine (combine (combine ms t1as) qss) prss) ->
        (forall tc2, In tc2 (combine (combine (combine ms t2as) qss) prss) -> In tc2 tc2s) ->
        (forall t12, In t12 (combine t1as t2as) -> Sub_typ e (fst t12) (snd t12)) ->
        Sub_typ e t1 t2
    | Sub_typ_iter : forall (e : E) t1 t2 it,
        (Sub_typ e t1 t2) ->
        Sub_typ e (typ_plain (plaintyp_ITER t1 it)) (typ_plain (plaintyp_ITER t2 it))
    | Sub_typ_refl : forall (e : E) t, Sub_typ e t t
    | Sub_typ_trans : forall (e : E) t1 t' t2,
        (Sub_typ e t1 t') ->
        (Sub_typ e t' t2) ->
        Sub_typ e t1 t2
with Sub_param : E -> param -> param -> subst -> Prop :=
    | Sub_param_exp : forall (e : E) x1 t1 x2 t2,
        (Sub_typ e t1 t2) ->
        Sub_param e (param_EXP x1 t1) (param_EXP x2 t2) (subst_EXP_generator [(x2, exp_VAR x1)])
    | Sub_param_typ : forall (e : E) x1 x2, Sub_param e (param_TYP x1) (param_TYP x2) (subst_TYP_generator [(x2, typ_VAR x1 nil)])
    | Sub_param_fun : forall (e : E) x1 ps1 t1 x2 ps2 t2 s,
        (Sub_params e ps2 ps1 s) ->
        (Sub_typ (concat_E e (paramenv ps2)) (subst_typ s t1) t2) ->
        Sub_param e (param_FUN x1 ps1 t1) (param_FUN x2 ps2 t2) (subst_FUN_generator [(x2, x1)])
    | Sub_param_gram : forall (e : E) x1 ps1 t1 x2 ps2 t2 s,
        (Sub_params e ps2 ps1 s) ->
        (Sub_typ (concat_E e (paramenv ps2)) (subst_typ s t1) t2) ->
        Sub_param e (param_GRAM x1 ps1 t1) (param_GRAM x2 ps2 t2) (subst_GRAM_generator [(x2, sym_VAR x1 nil)])
with Sub_params : E -> list param -> list param -> subst -> Prop :=
    | Sub_params_eps : forall (e : E), Sub_params e nil nil empty_subst
    | Sub_params_cons : forall (e : E) p1 p1s p2 p2s s s',
        (Sub_param e p1 p2 s) ->
        (Sub_params e p1s (map (fun p2' => subst_param s p2') p2s) s') ->
        Sub_params e (p1 :: p1s) (p2 :: p2s) (concat_subst s s')
with Ok_typ : E -> typ -> Prop :=
    | Ok_typ_optyp : forall E (op : optyp), Ok_typ E (typ_plain (plaintyp_op op))
    | Ok_typ_VAR : forall (e : E) x args ps insts s,
        (In (x, (ps, insts)) e.(S_TYP)) ->
        (Ok_args e args ps s) ->
        Ok_typ e (typ_VAR x args)
    | Ok_typ_TUP_empty : forall E, Ok_typ E (typ_plain (plaintyp_TUP nil))
    | Ok_typ_TUP_cons : forall (e : E) x1 t1 xts,
        (Ok_typ e t1) ->
        (Ok_typ (concat_E e (env_EXP_one x1 t1)) (typ_plain (plaintyp_TUP xts))) ->
        Ok_typ e (typ_plain (plaintyp_TUP ((x1, t1) :: xts)))
    | Ok_typ_ITER : forall E t it,
        (Ok_typ E t) ->
        (it = iter_QUEST \/ it = iter_STAR) ->
        Ok_typ E (typ_plain (plaintyp_ITER t it))
with Ok_deftyp : E -> deftyp -> Prop := 
    | Ok_deftyp_ALIAS : forall (e : E) t,
        (Ok_typ e t) ->
        Ok_deftyp e (deftyp_ALIAS t)
    | Ok_deftyp_STRUCT : forall (e : E) args ts qss prss,
        (forall tf, In tf (map (fun x => let '(((a, t), qs), prs) := x in (a, t, qs, prs)) (combine (combine (combine args ts) qss) prss)) -> Ok_typfield e tf) ->
        (disjoint args) ->
        Ok_deftyp e (deftyp_STRUCT (combine (combine (combine args ts) qss) prss))
    | Ok_deftyp_VARIANT : forall (e : E) ms ts qss prss,
        (forall tc, In tc (combine (combine (combine ms ts) qss) prss) -> Ok_typcase e tc) ->
        (disjoint ms) ->
        Ok_deftyp e (deftyp_VARIANT (map (fun x => let '(((m, t), qs), prs) := x in (m, t, qs, prs)) (combine (combine (combine ms ts) qss) prss)))
with Ok_typfield : E -> typfield -> Prop :=
    | Ok_typfield_prop : forall E (a : atom) (t : typ) (qs : list param) (prs : list prem),
        (Ok_typ E t) ->
        (Ok_params (concat_E E (tupenv t)) qs) ->
        (Ok_prems (concat_E E (concat_E (tupenv t) (paramenv qs))) prs) ->
        Ok_typfield E (a, t, qs, prs)
with Ok_typcase : E -> typcase -> Prop :=
    | Ok_typcase_prop : forall E m t qs prs,
        (Ok_typ E t) ->
        (Ok_params (concat_E E (tupenv t)) qs) ->
        (Ok_prems (concat_E E (concat_E (tupenv t) (paramenv qs))) prs) ->
        Ok_typcase E (m, t, qs, prs)
with Ok_iter : E -> iter -> iter -> E -> Prop :=
    | Ok_iter_QUEST : forall E, Ok_iter E iter_QUEST iter_QUEST empty_E
    | Ok_iter_STAR : forall E, Ok_iter E iter_STAR iter_STAR empty_E
    | Ok_iter_PLUS : forall E, Ok_iter E iter_PLUS iter_STAR empty_E
    | Ok_iter_SUP_Some : forall (e : E) x exp,
        (Ok_exp e exp (plaintyp_op (optyp_num numtyp_NAT))) ->
        Ok_iter e (iter_SUP (Some x) exp) iter_STAR (env_EXP_generator [])
    | Ok_iter_SUP_None : forall E e, Ok_iter E (iter_SUP None e) iter_STAR empty_E
with Ok_numunop : numunop -> numtyp -> numtyp -> Prop :=
    | Ok_numunop_sign : forall (op : numunop) nt,
        (Sub_numtyp numtyp_INT nt) ->
        Ok_numunop op nt nt
with Ok_numbinop : numbinop -> numtyp -> numtyp -> numtyp -> Prop :=
    | Ok_numbinop_ADD : forall nt, Ok_numbinop ADD nt nt nt
    | Ok_numbinop_SUB : forall nt nt',
        (Sub_numtyp numtyp_INT nt') ->
        Ok_numbinop SUB nt nt nt'
    | Ok_numbinop_MUL : forall nt, Ok_numbinop MUL nt nt nt
    | Ok_numbinop_IV : forall nt nt',
        (Sub_numtyp numtyp_RAT nt') ->
        Ok_numbinop DIV nt nt nt'
    | Ok_numbinop_MOD : forall nt,
        (Sub_numtyp nt numtyp_INT) ->
        Ok_numbinop MOD nt nt nt
    | Ok_numbinop_POW_NAT : forall nt, Ok_numbinop POW nt numtyp_NAT nt
    | Ok_numbinop_POW_INT : forall nt, 
        (Sub_numtyp nt numtyp_RAT) ->
        Ok_numbinop POW nt numtyp_INT nt
with Ok_exp : E -> exp -> typ -> Prop :=
    | Ok_exp_BOOL : forall E b, Ok_exp E (exp_BOOL b) (plaintyp_op BOOL)
    | Ok_exp_NAT : forall E n, Ok_exp E (exp_NUM (NAT n)) (typ_plain (plaintyp_op numtyp_NAT))
    | Ok_exp_INT : forall E i, Ok_exp E (exp_NUM (INT i)) (typ_plain (plaintyp_op numtyp_INT))
    | Ok_exp_RAT : forall E q, Ok_exp E (exp_NUM (RAT q)) (typ_plain (plaintyp_op numtyp_RAT))
    (*| Ok_exp_REAL : forall E r, Ok_exp E (exp_REAL r) (plaintyp_op numtyp_REAL)*)
    | Ok_exp_TEXT : forall E t, Ok_exp E (exp_TEXT t) (plaintyp_op TEXT)
    | Ok_exp_VAR : forall E x t,
        (In (x, t) E.(E_EXP)) ->
        Ok_exp E (exp_VAR x) t
    | Ok_exp_UN_BOOL : forall E (op : boolunop) e,
        (Ok_exp E e (typ_plain (plaintyp_op BOOL))) ->
        Ok_exp E (exp_UN op e) (typ_plain (plaintyp_op BOOL))
    | Ok_exp_UN_NUM : forall E (op : numunop) e (n n' : numtyp),
        (Ok_exp E e (typ_plain (plaintyp_op n))) ->
        (Ok_numunop op n n') ->
        Ok_exp E (exp_UN op e) (typ_plain (plaintyp_op n'))
    | Ok_exp_BIN_BOOL : forall E (op : boolbinop) e1 e2,
        (Ok_exp E e1 (typ_plain (plaintyp_op BOOL))) ->
        (Ok_exp E e2 (typ_plain (plaintyp_op BOOL))) ->
        Ok_exp E (exp_BIN op e1 e2) (typ_plain (plaintyp_op BOOL))
    | Ok_exp_BIN_NUM : forall E (op : numbinop) e1 e2 (n n1 n2 : numtyp),
        (Ok_exp E e1 (typ_plain (plaintyp_op n1))) ->
        (Ok_exp E e2 (typ_plain (plaintyp_op n2))) ->
        (Ok_numbinop op n1 n2 n) ->
        Ok_exp E (exp_BIN op e1 e2) (typ_plain (plaintyp_op n))
    | Ok_exp_CMP_POLY : forall E (op : polycmpop) e1 e2 t,
        (Ok_exp E e1 t) ->
        (Ok_exp E e2 t) ->
        Ok_exp E (exp_CMP op e1 e2) (typ_plain (plaintyp_op BOOL))
    | Ok_exp_CMP_NUM : forall E (op : numcmpop) e1 e2 (n : numtyp),
        (Ok_exp E e1 (typ_plain (plaintyp_op n))) ->
        (Ok_exp E e2 (typ_plain (plaintyp_op n))) ->
        Ok_exp E (exp_CMP op e1 e2) (typ_plain (plaintyp_op BOOL))
    | Ok_exp_TUP_eps : forall E, Ok_exp E (exp_TUP nil) (typ_plain (plaintyp_TUP nil))
    | Ok_exp_TUP_cons : forall E e1 es x1 t1 tbs,
        (Ok_exp E e1 t1) ->
        (Ok_exp E (exp_TUP es) (subst_typ (subst_EXP_generator [(x1, e1)]) (typ_plain (plaintyp_TUP tbs)))) ->
        Ok_exp E (exp_TUP (e1 :: es)) (typ_plain (plaintyp_TUP ((x1, t1) :: tbs)))
    | Ok_exp_OPT_Some : forall E e t,
        (Ok_exp E e t) ->
        (Ok_typ E t) ->
        Ok_exp E (exp_OPT (Some e)) (typ_plain (plaintyp_ITER t iter_QUEST))
    | Ok_exp_OPT_None : forall E t,
        (Ok_typ E t) ->
        Ok_exp E (exp_OPT None) (typ_plain (plaintyp_ITER t iter_QUEST))
    | Ok_exp_LIST : forall E es t,
        (forall e, In e es -> Ok_exp E e t) ->
        (Ok_typ E t) ->
        Ok_exp E (exp_LIST es) (typ_plain (plaintyp_ITER t iter_STAR))
    | Ok_exp_LIFT : forall E e t,
        (Ok_exp E e (typ_plain (plaintyp_ITER t iter_QUEST))) ->
        Ok_exp E (exp_LIFT e) (typ_plain (plaintyp_ITER t iter_STAR))
    | Ok_exp_INJ : forall (e : E) op e' x args tcs t qs prs,
        (Expand_typ e.(E_S) (typ_VAR x args) (deftyp_VARIANT tcs)) ->
        (In (((op, t), qs), prs) tcs) ->
        (Ok_exp e e' t) ->
        Ok_exp e (exp_INJ op e') (typ_VAR x args)
    | Ok_exp_STR : forall (e : E) x args ats ts qss prss es,
        (Expand_typ e.(E_S) (typ_VAR x args) (deftyp_STRUCT (combine (combine (combine ats ts) qss) prss))) ->
        (forall et, In et (combine es ts) -> Ok_exp e (fst et) (snd et)) ->
        Ok_exp e (exp_STR (combine ats es)) (typ_VAR x args)
    | Ok_exp_SEL : forall E e n tn ts xin xin',
        (Ok_exp E e (typ_plain (plaintyp_TUP (combine (xin ++ xin') ts)))) ->
        (List.length (xin ++ xin') = List.length ts) ->
        (find_nth n ts = Some tn) ->
        Ok_exp E (exp_SEL e n) (subst_typ (subst.subst_EXP_generator (combine xin (list_element (fun i => exp_SEL e i) (List.length xin)))) tn)
    | Ok_exp_LEN : forall E e t,
        (Ok_exp E e (typ_plain (plaintyp_ITER t iter_STAR))) ->
        Ok_exp E (exp_LEN e) (typ_plain (plaintyp_op numtyp_NAT))
    | Ok_exp_MEM : forall E e1 e2 t1,
        (Ok_exp E e1 t1) ->
        (Ok_exp E e2 (typ_plain (plaintyp_ITER t1 iter_STAR))) ->
        Ok_exp E (exp_MEM e1 e2) (typ_plain (plaintyp_op BOOL))
    | Ok_exp_CAT : forall E e1 e2 t,
        (Ok_exp E e1 (typ_plain (plaintyp_ITER t iter_STAR))) ->
        (Ok_exp E e2 (typ_plain (plaintyp_ITER t iter_STAR))) ->
        Ok_exp E (exp_CAT e1 e2) (typ_plain (plaintyp_ITER t iter_STAR))
    | Ok_exp_COMP : forall E e1 e2 t,
        (Ok_exp E e1 t) ->
        (Ok_exp E e2 t) ->
        (Composable_typ E t) ->
        Ok_exp E (exp_COMP e1 e2) t
    | Ok_exp_ACC : forall E e p t t',
        (Ok_exp E e t) ->
        (Ok_path E p t t') ->
        Ok_exp E (exp_ACC e p) t'
    | Ok_exp_UPD : forall E e1 p e2 t1 t2,
        (Ok_exp E e1 t1) ->
        (Ok_exp E e2 t2) ->
        (Ok_path E p t1 t1) ->
        Ok_exp E (exp_UPD e1 p e2) t1
    | Ok_exp_EXT : forall E e1 p e2 t1 t2,
        (Ok_exp E e1 t1) ->
        (Ok_exp E e2 (typ_plain (plaintyp_ITER t2 iter_STAR))) ->
        (Ok_path E p t1 (typ_plain (plaintyp_ITER t2 iter_STAR))) ->
        Ok_exp E (exp_EXT e1 p e2) t1
    | Ok_exp_CALL : forall (e : E) x args ps t cls s,
        (In (x, (ps, t, cls)) e.(S_FUN)) ->
        (Ok_args e args ps s) ->
        Ok_exp e (exp_CALL x args) (subst_typ s t)
    | Ok_exp_ITER : forall (e : E) E' e' it xs es t t's it',
        (Ok_iter e it it' E') ->
        (forall et', In et' (combine es t's) -> Ok_exp e (fst et') (plaintyp_ITER (snd et') it')) ->
        (Ok_exp (concat_E e (concat_E (env.env_EXP_generator (combine xs t's)) E')) e' t) ->
        (Ok_typ e t) ->
        Ok_exp e (exp_ITER e' it (combine xs es)) (typ_plain (plaintyp_ITER t it'))
    | Ok_exp_CVT : forall E e (nt1 nt2 : numtyp),
        (Ok_exp E e (typ_plain (plaintyp_op nt1))) ->
        Ok_exp E (exp_CVT e nt1 nt2) (typ_plain (plaintyp_op nt2))
    | Ok_exp_SUB : forall E e t1 t2,
        (Ok_exp E e t1) ->
        (Sub_typ E t1 t2) ->
        Ok_exp E (exp_SUB e t1 t2) t2
    | Ok_exp_conv : forall E e t t',
        (Ok_exp E e t') ->
        (Eq_typ E.(E_S) t t') ->
        Ok_exp E e t
with Ok_path : E -> path -> typ -> typ -> Prop :=
    | Ok_path_ROOT : forall (e : E) t,
        (Ok_typ e t) ->
        Ok_path e path_ROOT t t
    | Ok_path_THE : forall E p t t',
        (Ok_path E p t (typ_plain (plaintyp_ITER t' iter_QUEST))) ->
        Ok_path E (path_THE p) t t'
    | Ok_path_IDX : forall E p e t t',
        (Ok_path E p t (typ_plain (plaintyp_ITER t' iter_STAR))) ->
        (Ok_exp E e (typ_plain (plaintyp_op numtyp_NAT))) ->
        Ok_path E (path_IDX p e) t t'
    | Ok_path_SLICE : forall E p e1 e2 t t',
        (Ok_path E p t (typ_plain (plaintyp_ITER t' iter_STAR))) ->
        (Ok_exp E e1 (typ_plain (plaintyp_op numtyp_NAT))) ->
        (Ok_exp E e2 (typ_plain (plaintyp_op numtyp_NAT))) ->
        Ok_path E (path_SLICE p e1 e2) t t'
    | Ok_path_DOT : forall E p (a : atom) t t' x args qs prs tfs,
        (Ok_path E p t (typ_VAR x args)) ->
        (Expand_typ E.(E_S) (typ_VAR x args) (deftyp_STRUCT tfs)) ->
        (In (((a, t'), qs), prs) tfs) ->
        Ok_path E (path_DOT p a) t t'
    | Ok_path_PROJ : forall E p m t t' x args tcs qs prs,
        (Ok_path E p t (typ_VAR x args)) ->
        (Expand_typ E.(E_S) (typ_VAR x args) (deftyp_VARIANT tcs)) ->
        (In (((m, t'), qs), prs) tcs) ->
        Ok_path E (path_PROJ p m) t t'
    | Ok_path_conv : forall E p t t' t'',
        (Ok_path E p t'' t') ->
        (Eq_typ E.(E_S) t t'') ->
        Ok_path E p t t'
with Ok_sym : E -> sym -> typ -> Prop :=
    | Ok_sym_VAR : forall (e : E) x args s t ps prods,
        (In (x, (ps, t, prods)) e.(S_GRAM)) ->
        (Ok_args e args ps s) ->
        Ok_sym e (sym_VAR x args) (subst_typ s t)
    | Ok_sym_NUM : forall E n, Ok_sym E (sym_NUM n) (typ_plain (plaintyp_op numtyp_NAT))
    | Ok_sym_TEXT : forall E t, Ok_sym E (sym_TEXT t) (typ_plain (plaintyp_op TEXT))
    | Ok_sym_SEQ : forall E gs (ts : list typ),
        (forall gt, In gt (combine gs ts) -> Ok_sym E (fst gt) (snd gt)) ->
        Ok_sym E (sym_SEQ gs) (typ_plain (plaintyp_TUP nil))
    | Ok_sym_ALT : forall E gs (ts : list typ),
        (forall gt, In gt (combine gs ts) -> Ok_sym E (fst gt) (snd gt)) ->
        Ok_sym E (sym_ALT gs) (typ_plain (plaintyp_TUP nil))
    | Ok_sym_RANGE : forall E g1 g2,   
        (Ok_sym E g1 (typ_plain (plaintyp_op numtyp_NAT))) ->
        (Ok_sym E g2 (typ_plain (plaintyp_op numtyp_NAT))) ->
        Ok_sym E (sym_RANGE g1 g2) (typ_plain (plaintyp_op numtyp_NAT))
    | Ok_sym_ITER : forall (e : E) E' g it xs es t t's it',
        (Ok_iter e it it' E') ->
        (forall et', In et' (combine es t's) -> Ok_exp e (fst et') (plaintyp_ITER (snd et') it')) ->
        (Ok_sym (concat_E e (concat_E (env.env_EXP_generator (combine xs t's)) E')) g t) ->
        (Ok_typ e t) ->
        Ok_sym e (sym_ITER g it (combine xs es)) (typ_plain (plaintyp_ITER t it'))
    | Ok_sym_ATTR : forall E e g t,
        (Ok_sym E g t) ->
        (Ok_exp E e t) ->
        Ok_sym E (sym_ATTR e g) t
    | Ok_sym_conv : forall E g t t',
        (Ok_sym E g t') ->
        (Eq_typ E.(E_S) t t') ->
        Ok_sym E g t
with Ok_prem : E -> prem -> Prop :=
    | Ok_prem_RUEL : forall (e : E) x args e' ps t ruls s,
        (In (x, ((ps, t), ruls)) e.(S_REL)) ->
        (Ok_args e args ps s) ->
        (Ok_exp e e' (subst_typ s t)) ->
        Ok_prem e (prem_RULE x args e')
    | Ok_prem_IF : forall E e,
        (Ok_exp E e (typ_plain (plaintyp_op BOOL))) ->
        Ok_prem E (prem_IF e)
    | Ok_prem_ELSE : forall E, Ok_prem E prem_ELSE
    | Ok_prem_LET : forall E e1 e2 t,
        (Ok_exp E e1 t) ->
        (Ok_exp E e2 t) ->
        Ok_prem E (prem_LET e1 e2)
    | Ok_prem_ITER : forall (e : E) pr it xs es it' E' t's,
        (Ok_iter e it it' E') ->
        (forall et', In et' (combine es t's) -> Ok_exp e (fst et') (snd et')) ->
        (Ok_prem (concat_E e (concat_E (env.env_EXP_generator (combine xs t's)) E')) pr) ->
        Ok_prem e (prem_ITER pr it (combine xs es))
with Ok_prems : E -> list prem -> Prop :=
    | Ok_prems_prop : forall E prems,
        (forall prem, In prem prems -> Ok_prem E prem) ->
        Ok_prems E prems
with Ok_param : E -> param -> Prop :=
    | Ok_param_EXP : forall E x t,
        (Ok_typ E t) ->
        Ok_param E (param_EXP x t)
    | Ok_param_TYP : forall E x, Ok_param E (param_TYP x)
    | Ok_param_FUN : forall E x ps t,
        (Ok_params E ps) ->
        (Ok_typ (concat_E E (paramenv ps)) t) ->
        Ok_param E (param_FUN x ps t)
    | Ok_param_GRAM : forall E x ps t,
        (Ok_params E ps) ->
        (Ok_typ (concat_E E (paramenv ps)) t) ->
        Ok_param E (param_GRAM x ps t)
with Ok_params : E -> list param -> Prop :=
    | Ok_params_empty : forall E, Ok_params E nil
    | Ok_params_cons : forall E p1 ps,
        (Ok_param E p1) ->
        (Ok_params (concat_E E (paramenv [p1])) ps) ->
        Ok_params E (p1 :: ps)
with Ok_arg : E -> arg -> param -> subst -> Prop :=
    | Ok_arg_EXP : forall E e x t,
        (Ok_exp E e t) ->
        Ok_arg E (arg_EXP e) (param_EXP x t) (subst.subst_EXP_generator [(x, e)])
    | Ok_arg_TYP : forall E t x,
        (Ok_typ E t) ->
        Ok_arg E (arg_TYP t) (param_TYP x) (subst.subst_TYP_generator [(x, t)])
    | Ok_arg_FUN : forall (e : E) y x ps t t' clauses p's s,
        (In (y, (p's, t', clauses)) e.(S_FUN)) ->
        (Sub_params e ps p's s) ->
        (Sub_typ e (subst_typ s t') t) ->
        Ok_arg e (arg_FUN y) (param_FUN x ps t) (subst_FUN_generator [(x, y)])
    | Ok_arg_GRAM_ground : forall E g x t,
        (Ok_sym E g t) ->
        Ok_arg E (arg_GRAM g) (param_GRAM x nil t) (subst_GRAM_generator [(x, g)])
    | Ok_arg_GRAM_higher : forall (e : E) y x ps t p's t' prods s,
        (In (y, (p's, t', prods)) e.(S_GRAM)) ->
        (Sub_params e ps p's s) ->
        (Sub_typ e (subst_typ s t') t) ->
        Ok_arg e (arg_GRAM (sym_VAR y nil)) (param_GRAM x ps t) (subst_GRAM_generator [(x, sym_VAR y nil)]) 
with Ok_args : E -> list arg -> list param -> subst -> Prop :=
    | Ok_args_empty : forall E, Ok_args E nil nil empty_subst
    | Ok_args_cons : forall E arg1 args p1 ps s1 s,
        (Ok_arg E arg1 p1 s1) ->
        (Ok_args E args (map (fun p => subst_param s p) ps) s) ->
        Ok_args E (arg1 :: args) (p1 :: ps) (concat_subst s1 s)
with Ok_subst : E -> subst -> list quant -> Prop :=
    | Ok_subst_prop : forall (e : E) s qs (ss : list subst),
        (List.length qs = List.length ss) ->
        (forall (p : param * subst), In p (combine qs ss) ->
          Ok_arg e (subst_arg s (paramarg (fst p))) (subst_param s (fst p)) (snd p)) ->
        Ok_subst e s qs
with Ok_dec : E -> dec -> E -> Prop :=
    | Ok_dec_TYP : forall E x ps insts,
        (Ok_params E ps) ->
        (forall inst, In inst insts -> Ok_inst E inst ps) ->
        Ok_dec E (dec_TYP x ps insts) (concat_E E (env_TYP_generator [(x, (ps, insts))]))
    | Ok_dec_REL : forall E x ps t ruls,
        (Ok_params E ps) ->
        (forall rul, In rul ruls -> Ok_rule (concat_E E (paramenv ps)) rul t) ->
        Ok_dec E (dec_REL x ps t ruls) (concat_E E (env_REL_generator [(x, ((ps, t), ruls))]))
    | Ok_dec_FUN : forall E x ps t clauses,
        (Ok_params E ps) ->
        (forall clause, In clause clauses -> Ok_clause (concat_E E (paramenv ps)) clause ps t) ->
        Ok_dec E (dec_FUN x ps t clauses) (concat_E E (env_FUN_generator [(x, ((ps, t), clauses))]))
    | Ok_dec_GRAM : forall E x ps t prods,
        (Ok_params E ps) ->
        (forall pro, In pro prods -> Ok_prod (concat_E E (paramenv ps)) pro t) ->
        Ok_dec E (dec_GRAM x ps t prods) (concat_E E (env_GRAM_generator [(x, ((ps, t), prods))]))
    | Ok_dec_REC : forall E ds E',
        (Ok_decs (concat_E E E') ds E') ->
        Ok_dec E (dec_REC ds) E'
with Ok_decs : E -> list dec -> E -> Prop :=
    | Ok_decs_empty : forall E, Ok_decs E nil empty_E
    | Ok_decs_cons : forall E d1 ds E1 E',
        (Ok_dec E d1 E1) ->
        (Ok_decs (concat_E E E1) ds E') ->
        Ok_decs E (d1 :: ds) (concat_E E1 E')
with Ok_inst : E -> inst -> list param -> Prop :=
    | Ok_inst_prop : forall E qs args dt ps s,
        (Ok_params E qs) ->
        (Ok_args (concat_E E (paramenv qs)) args ps s) ->
        (Ok_deftyp (concat_E E (paramenv qs)) dt) ->
        Ok_inst E (INST qs args dt) ps
with Ok_rule : E -> rul -> typ -> Prop :=
    | Ok_rule_prop : forall E qs e prs t,
        (Ok_params E qs) ->
        (Ok_exp (concat_E E (paramenv qs)) e t) ->
        (Ok_prems (concat_E E (paramenv qs)) prs) ->
        Ok_rule E (RULE qs e prs) t
with Ok_clause : E -> clause -> list param -> typ -> Prop :=
    | Ok_clause_prop : forall E qs args e prs ps s t,
        (Ok_params E qs) ->
        (Ok_args (concat_E E (paramenv qs)) args ps s) ->
        (Ok_exp (concat_E E (paramenv qs)) e t) ->
        (Ok_prems (concat_E E (paramenv qs)) prs) ->
        Ok_clause E (CLAUSE qs args e prs) ps t
with Ok_prod : E -> prod -> typ -> Prop :=
    | Ok_prod_prop : forall E qs g e prs t t',
        (Ok_params E qs) ->
        (Ok_sym (concat_E E (paramenv qs)) g t') ->
        (Ok_exp (concat_E E (paramenv qs)) e t) ->
        (Ok_prems (concat_E E (paramenv qs)) prs) ->
        Ok_prod E (PROD qs g e prs) t.

Inductive Ok_script : script -> Prop :=
    | Ok_script_prop : forall E ds,
        (Ok_decs empty_E ds E) ->
        Ok_script ds.