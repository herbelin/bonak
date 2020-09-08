Require Import Interface.

Module LeSPropInd.

Inductive le' (n : nat) : nat -> SProp :=
  | le_refl : n <= n
  | le_S_up : forall {m : nat}, n <= m -> n <= S m
  where "n <= m" := (le' n m) : nat_scope.

Definition le := le'.

Arguments le_S_up {n m}.

Notation "↑ h" := (le_S_up h) (at level 40).

Theorem le_trans {p q n} : p <= q -> q <= n -> p <= n.
  intros G H.
  induction H as [|r].
  - exact G.
  - apply le_S_up; exact IHle'.
Defined.

Infix "↕" := le_trans (at level 30).

Theorem le_adjust {p n} : S p <= S n -> p <= n.
  intros G.
  change n with (pred (S n)).
  induction G.
  - apply le_refl.
  - destruct m.
    * assumption.
    * apply (↑ IHG).
Defined.

Definition le_S_down {p n} (Hp : S p <= n) : p <= n := le_adjust (↑ Hp).

Notation "⇓ p" := (le_S_down p) (at level 40).

Inductive sFalse : SProp :=.
Inductive sTrue : SProp := SI.

Theorem le_discr {n} (H : S n <= 0) {A:Type} : A.
Proof.
apply sFalse_rect.
change (match 0 with 0 => sFalse | S _ => sTrue end).
induction H; exact SI.
Defined.

End LeSPropInd.
