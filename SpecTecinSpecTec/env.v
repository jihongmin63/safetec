Require Import syntax.
From Stdlib Require Import List.
Import ListNotations.

Definition typdef := ((list param) * (list inst))%type.
Definition fundef := ((list param) * typ * (list clause))%type.
Definition reldef := ((list param) * typ * (list rul))%type.
Definition gramdef := ((list param) * typ * (list prod))%type.

Record S := {
    S_TYP : list (id * typdef);
    S_FUN : list (id * fundef);
    S_REL : list (id * reldef);
    S_GRAM : list (id * gramdef)
}.

Record E := {
    E_S :> S;
    E_EXP : list (id * typ)
}.

Definition concat_S (S1 S2 : S) : S :=
    {|
        S_TYP := S1.(S_TYP) ++ S2.(S_TYP);
        S_FUN := S1.(S_FUN) ++ S2.(S_FUN);
        S_REL := S1.(S_REL) ++ S2.(S_REL);
        S_GRAM := S1.(S_GRAM) ++ S2.(S_GRAM)
    |}.

Definition concat_E (E1 E2 : E) : E :=
    {|
        E_S := concat_S E1.(E_S) E2.(E_S);
        E_EXP := E1.(E_EXP) ++ E2.(E_EXP)
    |}.

Fixpoint composeenvs (es : list E) : E :=
  match es with
  | nil =>
    (let empty_s := {| S_TYP := @nil (id * typdef); S_FUN := @nil (id * fundef); S_REL := @nil (id * reldef); S_GRAM := @nil (id * gramdef) |} in
     {| E_S := empty_s; E_EXP := @nil (id * typ) |})
  | cons e es' =>
    concat_E e (composeenvs es')
  end.

Definition storenv (Store : S) : E := {| E_S := Store; E_EXP := @nil (id * typ) |}.

Definition tupenv (t : typ) : E :=
    match t with
    | plaintyp_TUP l =>
      let empty_s := {| S_TYP := @nil (id * typdef); S_FUN := @nil (id * fundef); S_REL := @nil (id * reldef); S_GRAM := @nil (id * gramdef) |} in
      {| E_S := empty_s; E_EXP := l |}
    | _ =>
      let empty_s := {| S_TYP := @nil (id * typdef); S_FUN := @nil (id * fundef); S_REL := @nil (id * reldef); S_GRAM := @nil (id * gramdef) |} in
      {| E_S := empty_s; E_EXP := @nil (id * typ) |}
    end.

Definition paramenv (ps : list param) : E :=
    composeenvs (map (fun p =>
        match p with
        | param_EXP x t =>
          let empty_s := {| S_TYP := @nil (id * typdef); S_FUN := @nil (id * fundef); S_REL := @nil (id * reldef); S_GRAM := @nil (id * gramdef) |} in
          {| E_S := empty_s; E_EXP := [(x, t)] |}
        | param_TYP x =>
          {| E_S := {|
                S_TYP := [(x, ([], []))]; S_FUN := @nil (id * fundef); S_REL := @nil (id * reldef); S_GRAM := @nil (id * gramdef)
            |};
            E_EXP := @nil (id * typ)
          |}
        | param_FUN x ps' t =>
          {| E_S := {|
                S_TYP := @nil (id * typdef); S_FUN := [(x, (ps', t, []))]; S_REL := @nil (id * reldef); S_GRAM := @nil (id * gramdef)
            |};
            E_EXP := @nil (id * typ)
          |}
        | param_GRAM x ps' t =>
          {| E_S := {|
                S_TYP := @nil (id * typdef); S_FUN := @nil (id * fundef); S_REL := @nil (id * reldef); S_GRAM := [(x, (ps', t, []))]
            |};
            E_EXP := @nil (id * typ)
          |}
        end
    ) ps).