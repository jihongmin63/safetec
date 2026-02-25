Require Import syntax.
Require Import env.

From Stdlib Require Import Nat.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.
From Stdlib Require Import Bool.
From Stdlib Require Import Floats.

Definition boolun (op : boolunop) (b : bool) : bool :=
    match op with
    | NOT => negb b
    end.

Definition boolbin (op : boolbinop) (b1 b2 : bool) : bool :=
    match op with
    | AND => andb b1 b2
    | OR => orb b1 b2
    | IMPL => implb b1 b2
    | EQUIV => Bool.eqb b1 b2
    end.

Definition iszero (x : syntax.num) : bool :=
    match x with
    | NAT n => Nat.eqb n 0
    | INT i => Z.eqb i 0
    | RAT q => Qeq_bool q 0
    (*| REAL r => PrimFloat.eqb r 0%float*)
    end.

Definition isone (x : syntax.num) : bool :=
    match x with
    | NAT n => Nat.eqb n 1
    | INT i => Z.eqb i 1
    | RAT q => Qeq_bool q 1
    (*| REAL r => PrimFloat.eqb r 1%float*)
    end.


Fixpoint numcvt_aux (fuel : nat) (t : syntax.numtyp) (x : syntax.num) : option syntax.num :=
    match fuel with
    | 0%nat => None
    | Datatypes.S fuel' =>
        match t with
        | numtyp_NAT =>
            match x with
            | NAT n => Some (NAT n)
            | INT i =>
              if Z.geb i 0 then Some (NAT (Z.to_nat i)) else None
            | RAT q =>
              match (numcvt_aux fuel' numtyp_INT x) with
              | Some n => numcvt_aux fuel' numtyp_NAT n
              | None => None
              end
            (*| REAL r => numcvt_aux fuel' numtyp_NAT (numcvt_aux fuel' numtyp_RAT x)*)
            end
        | numtyp_INT =>
            match x with
            | NAT n => Some (INT (Z.of_nat n))
            | INT i => Some (INT i)
            | RAT q =>
              let (n, d) := q in
              if Z.eqb (Z.modulo n (Z.pos d)) 0 then Some (INT (Z.div n (Z.pos d))) else None
            (*| REAL r => numcvt_aux fuel' numtyp_INT (numcvt_aux fuel' numtyp_RAT x)*)
            end
        | numtyp_RAT =>
            match x with
            | NAT n => Some (RAT (inject_Z (Z.of_nat n)))
            | INT i => Some (RAT (inject_Z i))
            | RAT q => Some (RAT q)
            (*| REAL r =>*)
            end
        (*| numtyp_REAL =>
            match x with
            | NAT n =>
            | INT i =>
            | RAT q =>
            | REAL r => Some (REAL r)
            end*)
        end
    end.

Definition numcvt (t : syntax.numtyp) (x : syntax.num) : option syntax.num :=
    numcvt_aux 4 t x.

Definition numun (t : numunop) (x : syntax.num) : syntax.num :=
    match t with
    | PLUS => x
    | MINUS =>
        match x with
        | NAT n => INT (-(Z.of_nat n))
        | INT i => INT (-i)
        | RAT q => RAT (-q)
        (*| REAL r => REAL (-r)*)
        end
    end.

Definition numbin (t : numbinop) (x1 x2 : syntax.num) : option syntax.num :=
    match t with
    | ADD =>
        match x1, x2 with
        | NAT n1, NAT n2 => Some (NAT (n1 + n2))
        | INT i1, INT i2 => Some (INT (i1 + i2))
        | RAT q1, RAT q2 => Some (RAT (q1 + q2))
        (*| REAL r1, REAL r2 => REAL (r1 + r2)*)
        | _, _ => None
        end
    | SUB =>
        match x1, x2 with
        | NAT n1, NAT n2 =>
          if n2 <=? n1 then Some (NAT (n1 - n2)) else None
        | INT i1, INT i2 => Some (INT (i1 - i2))
        | RAT q1, RAT q2 => Some (RAT (q1 - q2))
        (*| REAL r1, REAL r2 => REAL (r1 - r2)*)
        | _, _ => None
        end
    | MUL =>
        match x1, x2 with
        | NAT n1, NAT n2 => Some (NAT (n1 * n2))
        | INT i1, INT i2 => Some (INT (i1 * i2))
        | RAT q1, RAT q2 => Some (RAT (q1 * q2))
        (*| REAL r1, REAL r2 => REAL (r1 * r2)*)
        | _, _ => None
        end
    | DIV =>
        if iszero x2 then None else
        match x1, x2 with
        | NAT n1, NAT n2 =>
          if Nat.eqb (Nat.modulo n1 n2) 0 then Some (NAT (n1 / n2)) else None
        | INT i1, INT i2 =>
          if Z.eqb (Z.rem i1 i2) 0 then Some (INT (i1 / i2)) else None
        | RAT q1, RAT q2 => Some (RAT (q1 / q2))
        (*| REAL r1, REAL r2 => REAL (r1 / r2)*)
        | _, _ => None
        end
    | MOD =>
        if iszero x2 then None else
        match x1, x2 with
        | NAT n1, NAT n2 => Some (NAT (Nat.modulo n1 n2))
        | INT i1, INT i2 => Some (INT (Z.rem i1 i2))
        | _, _ => None
        end
    | POW =>
        match x1, x2 with
        | NAT n1, NAT n2 => Some (NAT (n1 ^ n2))
        | INT i1, INT i2 =>
          if Z.geb i2 0 then Some (INT (i1 ^ i2)) else None
        | RAT q1, RAT q2 =>
          let (n, d) := q2 in
          if Z.eqb (Z.modulo n (Z.pos d)) 0 then Some (RAT (q1 ^ (Z.div n (Z.pos d))))
          else None
        (*| REAL r1, REAL r2 => REAL (r1 + r2)*)
        | _, _ => None
        end
    end.

Definition numcmp (op : numcmpop) (x1 x2 : syntax.num) : option bool :=
    match op with
    | LT =>
      match x1, x2 with
      | NAT n1, NAT n2 => Some (Nat.ltb n1 n2)
      | INT i1, INT i2 => Some (Z.ltb i1 i2)
      | RAT q1, RAT q2 => Some (match Qcompare q1 q2 with Lt => true | _ => false end)
      (*| REAL r1, REAL r2 => Some (PrimFloat.ltb r1 r2)*)
      | _, _ => None
      end
    | GT =>
      match x1, x2 with
      | NAT n1, NAT n2 => Some (Nat.ltb n2 n1)
      | INT i1, INT i2 => Some (Z.gtb i1 i2)
      | RAT q1, RAT q2 => Some (match Qcompare q1 q2 with Gt => true | _ => false end)
      (*| REAL r1, REAL r2 => Some (PrimFloat.gtb r1 r2)*)
      | _, _ => None
      end
    | LE =>
      match x1, x2 with
      | NAT n1, NAT n2 => Some (Nat.leb n1 n2)
      | INT i1, INT i2 => Some (Z.leb i1 i2)
      | RAT q1, RAT q2 => Some (match Qcompare q1 q2 with Gt => false | _ => true end)
      (*| REAL r1, REAL r2 => Some (PrimFloat.leb r1 r2)*)
      | _, _ => None
      end
    | GE =>
      match x1, x2 with
      | NAT n1, NAT n2 => Some (Nat.leb n2 n1)
      | INT i1, INT i2 => Some (Z.geb i1 i2)
      | RAT q1, RAT q2 => Some (match Qcompare q1 q2 with Lt => false | _ => true end)
      (*| REAL r1, REAL r2 => Some (PrimFloat.leb r2 r1)*)
      | _, _ => None
      end
    end.