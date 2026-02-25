From Stdlib Require Import List.
From Stdlib Require Import String.
From Stdlib Require Import Nat.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.
From Stdlib Require Import Floats.

Definition id := string.
Definition atom := string.
Definition mixop := list (list atom).

Inductive booltyp :=
    | BOOL.
    
Inductive numtyp :=
    | numtyp_NAT
    | numtyp_INT
    | numtyp_RAT
    (*| numtyp_REAL*).

Inductive texttyp :=
    | TEXT.

Inductive optyp :=
    | optyp_bool : (booltyp) -> optyp
    | optyp_num : (numtyp) -> optyp
    | optyp_test : (texttyp) -> optyp.
Coercion optyp_bool : booltyp >-> optyp.
Coercion optyp_num : numtyp >-> optyp.
Coercion optyp_test : texttyp >-> optyp.

Inductive num :=
    | NAT : (nat) -> num
    | INT : (Z) -> num
    | RAT : (Q) -> num
    (*| REAL : (float) -> num*).

Inductive boolunop :=
    | NOT.

Inductive boolbinop :=
    | AND
    | OR
    | IMPL
    | EQUIV.

Inductive numunop :=
    | PLUS
    | MINUS.

Inductive numbinop :=
    | ADD
    | SUB
    | MUL
    | DIV
    | MOD
    | POW.

Inductive numcmpop :=
    | LT
    | GT
    | LE
    | GE.

Inductive polycmpop :=
    | EQ
    | NE.

Inductive unop :=
    | unop_bool (b : boolunop)
    | unop_num (n : numunop).
Coercion unop_bool : boolunop >-> unop.
Coercion unop_num : numunop >-> unop.

Inductive binop :=
    | binop_bool (b : boolbinop)
    | binop_num (n : numbinop).
Coercion binop_bool : boolbinop >-> binop.
Coercion binop_num : numbinop >-> binop.

Inductive cmpop :=
    | cmpop_poly (p : polycmpop)
    | cmpop_num (n : numcmpop).
Coercion cmpop_poly : polycmpop >-> cmpop.
Coercion cmpop_num : numcmpop >-> cmpop.

Inductive plaintyp :=
    | plaintyp_op : (optyp) -> plaintyp
    | plaintyp_TUP : (list (id * typ)) -> plaintyp
    | plaintyp_ITER : (typ) -> (iter) -> plaintyp
with typ :=
    | typ_plain : (plaintyp) -> typ
    | typ_VAR : (id) -> (list arg) -> typ
with deftyp :=
    | deftyp_ALIAS : (typ) -> deftyp
    | deftyp_STRUCT : (list (atom * typ * (list param) * (list prem))) -> deftyp
    | deftyp_VARIANT : (list (mixop * typ * (list param) * (list prem))) -> deftyp
with iter :=
    | iter_QUEST : iter
    | iter_STAR : iter
    | iter_PLUS : iter
    | iter_SUP : (option id) -> (exp) -> iter
with val :=
    | val_NUM  : (num) -> val
    | val_BOOL : (bool) -> val
    | val_TEXT : (string) -> val
    | val_TUP : (list val) -> val
    | val_INJ : (mixop) -> (val) -> val
    | val_OPT : (option val) -> val
    | val_LIST : (list val) -> val
    | val_STR : (list (atom * val)) -> val
with exp :=
    | exp_NUM : (num) -> exp
    | exp_VAR : (id) -> exp
    | exp_BOOL : (bool) -> exp
    | exp_TEXT : (string) -> exp
    | exp_UN : (unop) -> (exp) -> exp
    | exp_BIN : (binop) -> (exp) -> (exp) -> exp
    | exp_CMP : (cmpop) -> (exp) -> (exp) -> exp
    | exp_TUP : (list exp) -> exp
    | exp_INJ : (mixop) -> (exp) -> exp
    | exp_OPT : (option exp) -> exp
    | exp_LIST : (list exp) -> exp
    | exp_LIFT : (exp) -> exp
    | exp_STR : (list (atom * exp)) -> exp
    | exp_SEL : (exp) -> (nat) -> exp
    | exp_LEN : (exp) -> exp
    | exp_MEM : (exp) -> (exp) -> exp
    | exp_CAT : (exp) -> (exp) -> exp
    | exp_COMP : (exp) -> (exp) -> exp
    | exp_ACC : (exp) -> (path) -> exp
    | exp_UPD : (exp) -> (path) -> (exp) -> exp
    | exp_EXT : (exp) -> (path) -> (exp) -> exp
    | exp_CALL : (id) -> (list arg) -> exp
    | exp_ITER : (exp) -> (iter) -> (list (id * exp)) -> exp
    | exp_CVT : (exp) -> (numtyp) -> (numtyp) -> exp
    | exp_SUB : (exp) -> (typ) -> (typ) -> exp
with path :=
    | path_ROOT : path
    | path_THE : (path) -> path
    | path_IDX : (path) -> (exp) -> path
    | path_SLICE : (path) -> (exp) -> (exp) -> path
    | path_DOT : (path) -> (atom) -> path
    | path_PROJ : (path) -> (mixop) -> path
with sym :=
    | sym_VAR : (id) -> (list arg) -> sym
    | sym_NUM : (nat) -> sym
    | sym_TEXT : (string) -> sym
    | sym_SEQ : (list sym) -> sym
    | sym_ALT : (list sym) -> sym
    | sym_RANGE : (sym) -> (sym) -> sym
    | sym_ITER : (sym) -> (iter) -> (list (id * exp)) -> sym
    | sym_ATTR : (exp) -> (sym) -> sym
with arg :=
    | arg_EXP : (exp) -> arg
    | arg_TYP : (typ) -> arg
    | arg_FUN : (id) -> arg
    | arg_GRAM : (sym) -> arg
with param :=
    | param_EXP : (id) -> (typ) -> param
    | param_TYP : (id) -> param
    | param_FUN : (id) -> (list param) -> (typ) -> param
    | param_GRAM : (id) -> (list param) -> (typ) -> param
with prem :=
    | prem_RULE : (id) -> (list arg) -> (exp) -> prem
    | prem_IF : (exp) -> prem
    | prem_ELSE : prem
    | prem_LET : (exp) -> (exp) -> prem
    | prem_ITER : (prem) -> (iter) -> (list (id * exp)) -> prem
with dec :=
    | dec_TYP : (id) -> (list param) -> (list inst) -> dec
    | dec_REL : (id) -> (list param) -> (list rul) -> dec
    | dec_FUN : (id) -> (list param) -> (list clause) -> dec
    | dec_GRAM : (id) -> (list param) -> (list prod) -> dec
    | dec_REC : (list dec) -> dec
with inst :=
    | INST : (list param) -> (list arg) -> (deftyp) -> inst
with rul :=
    | RULE : (list param) -> (exp) -> (list prem) -> rul
with clause :=
    | CLAUSE : (list param) -> (list arg) -> (exp) -> (list prem) -> clause
with prod :=
    | PROD : (list param) -> (sym) -> (exp) -> (list prem) -> prod.

Coercion plaintyp_op : optyp >-> plaintyp.
Coercion typ_plain : plaintyp >-> typ.
Coercion val_NUM : num >-> val.
Coercion exp_NUM : num >-> exp.


Definition quant := param.
Definition typbind := (id * typ)%type.
Definition typfield := (atom * typ * (list quant) * (list prem))%type.
Definition typcase := (mixop * typ * (list quant) * (list prem))%type.

Definition valfield := (atom * val)%type.

Definition expfield := (atom * exp)%type.
Definition exppull := (id * exp)%type.

Definition script := list dec.