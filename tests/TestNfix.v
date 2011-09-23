Require Import Nfix.
Require Import List.

Module ExemplesSimples.
  Inductive term :=
  | app (f : nat) (l : list term).

  Nested Fixpoint term_size (t : term) (acc : nat) : nat :=
    match t with
      | app _ l => term_list_size l (S acc)
    end
  with term_list_size (l : list term) (acc : nat) : nat :=
    match l with
      | nil => acc
      | t::q => term_list_size q (term_size t acc)
    end.
  Print term_list_size_.
  Print term_size.
  Print term_list_size.

  Inductive formula :=
  | atom (P : Prop)
  | cnf (clauses : list (list formula)).

  Nested Fixpoint formula_interp (f : formula) : Prop :=
    match f with
      | atom P => P
      | cnf cl => formula_ll_interp cl
    end
  with formula_l_interp (l : list formula) : Prop :=
    match l with
      | nil => False
      | f::q => formula_interp f \/ formula_l_interp q
    end
  with formula_ll_interp (ll : list (list formula)) : Prop :=
    match ll with
      | nil => True
      | c::q => formula_l_interp c /\ formula_ll_interp q
    end.
  Print formula_l_interp_.
  Print formula_ll_interp_.
  Print formula_interp.
  Print formula_l_interp.
  Print formula_ll_interp.
End ExemplesSimples.

Module ExemplesDuMail.
  Inductive term : Type :=
  | c : nat -> term
  | node : lterm -> term
  | node2 : list term -> term
  with lterm : Type :=
  | null : lterm
  | add : term -> lterm -> lterm.

  Section Elimination.
    Variable P : term -> Type.
    Variable Q : lterm -> Type.
    Variable R : list term -> Type.
    Variable Pc : forall n : nat, P (c n).
    Variable Pnode : forall l : lterm, Q l -> P (node l).
    Variable Pnode2 : forall l : list term, R l -> P (node2 l).
    Variable Qnull : Q null.
    Variable Qadd : forall (t:term) (l:lterm), P t -> Q l -> Q (add t l).
    Variable Rnil : R nil.
    Variable Rcons : forall (t:term) (l:list term), P t -> R l -> R (cons t l).

    Nested Fixpoint f (t : term) : P t :=
      match t return P t with
        | c n => Pc n
        | node l => Pnode l (lf l)
        | node2 l => Pnode2 l (lf2 l)
      end
    with lf (l : lterm) : Q l :=
      match l return Q l with
        | null => Qnull
        | add t l1 => Qadd t l1 (f t) (lf l1)
      end
    with lf2 (l : list term) : R l :=
      match l return R l with
        | nil => Rnil
        | t::l1 => Rcons t l1 (f t) (lf2 l1)
      end.

    Goal forall lt:lterm, f (node lt) = Pnode lt (lf lt).
      trivial.
    Qed.

    Goal forall lt:list term, f (node2 lt) = Pnode2 lt (lf2 lt).
      trivial.
    Qed.

    Goal forall (t:term) (lt:lterm), lf (add t lt) = Qadd t lt (f t) (lf lt).
      trivial.
    Qed.

    Goal forall (t:term) (lt:list term),
      lf2 (cons t lt) = Rcons t lt (f t) (lf2 lt).
      trivial.
    Qed.
  End Elimination.

  Inductive term2 : Type :=
  | c2 : nat -> term2
  | n2 : list (term2 * lterm2) -> term2
  with lterm2 : Type :=
  | null2 : lterm2
  | add2 : term2 -> lterm2 -> lterm2.

  Section Elimination2.
    Variable P : term2 -> Type.
    Variable Q : lterm2 -> Type.
    Variable T : term2 * lterm2 -> Type.
    Variable R : list (term2 * lterm2) -> Type.
    Variable Pc : forall n : nat, P (c2 n).
    Variable Pn2 : forall l : list (term2 * lterm2), R l -> P (n2 l).
    Variable Qnull : Q null2.
    Variable Qadd : forall (t:term2) (l:lterm2), P t -> Q l -> Q (add2 t l).
    Variable Tpair : forall (t:term2) (lt:lterm2), P t -> Q lt -> T (t,lt).
    Variable Rnil : R nil.
    Variable Rcons : forall (t:term2*lterm2) (l:list (term2 * lterm2)),
      T t -> R l -> R (cons t l).

    Nested Fixpoint fP (t : term2) : P t :=
      match t return P t with
        | c2 n => Pc n
        | n2 l => Pn2 l (fR l)
      end
    with fQ (l : lterm2) : Q l :=
      match l return Q l with
        | null2 => Qnull
        | add2 t l1 => Qadd t l1 (fP t) (fQ l1)
      end
    with fT (p : term2 * lterm2) : T p :=
      match p return T p with
        | (t, l) => Tpair t l (fP t) (fQ l)
      end
    with fR (l : list (term2 * lterm2)) : R l :=
      match l return R l with
        | nil => Rnil
        | cons p l1 => Rcons p l1 (fT p) (fR l1)
      end.

    Goal forall lt, fP (n2 lt) = Pn2 lt (fR lt).
      trivial.
    Qed.

    Goal forall t lt, fR (cons t lt) = Rcons t lt (fT t) (fR lt).
      trivial.
    Qed.

    Goal forall t lt, fT (t,lt) = Tpair t lt (fP t) (fQ lt).
      trivial.
    Qed.
  End Elimination2.
End ExemplesDuMail.

(* Module ExemplesQuiPassentPas. *)
(*   Require Import List. *)
(*   Inductive term (symbols : Type) := *)
(*   | app (f : symbols) (l : list (term symbols)). *)
(*   Inductive recsymbol : Type := *)
(*   | symb : nat -> recsymbol *)
(*   | recsymb : term recsymbol -> recsymbol. *)

(*   Nested Fixpoint rs_size (s : recsymbol) : nat := *)
(*     match s with *)
(*       | symb n => 1 *)
(*       | recsymb ts => ts_size ts *)
(*     end *)
(*     with ts_size (ts : term recsymbol) : nat := *)
(*       match ts with *)
(*         | app f l => rs_size f + lts_size l *)
(*       end *)
(*     with lts_size (lts : list (term recsymbol)) : nat := *)
(*       match lts with *)
(*         | nil => O *)
(*         | ts::q => ts_size ts + lts_size q *)
(*       end. *)
(* End ExemplesQuiPassentPas. *)
