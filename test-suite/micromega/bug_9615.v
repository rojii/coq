Require Import ZArith Lia. Local Open Scope Z_scope.

Unset Lia Cache.

Goal forall
    (q r lx q0 r0 : Z)
    (H : 8 * lx = 2 ^ 4 * q + r)
    (H1 : q * 2 ^ 3 = 8 * q0 + r0)
    (H3 : 0 <= r)
    (H4 : r < 2 ^ 4)
    (H0 : 0 <= r0)
    (H5 : r0 < 8),
    q * 2 ^ 3 = 8 * q0.
Proof.
  intros.
  Lia.lia.
Qed.

Goal
  forall q r lx : Z,
  8 * lx = 2 ^ 4 * q + r ->
  0 <= r < 2 ^ 4 ->
  forall q0 r0 : Z,
  q * 2 ^ 3 = 8 * q0 + r0 -> 0 <= r0 < 8 -> q * 2 ^ 3 = 8 * q0.
Proof.
  intros.
  Lia.lia.
Qed.
