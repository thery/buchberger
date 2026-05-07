(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Load hOrder.

Local Hint Resolve ltT_not_ltT : core.
Local Hint Resolve ltT_not_eqT : core.
Definition eqT_not_ltT :=  (eqT_not_ltT A n ltM).
Local Hint Resolve eqT_not_ltT : core.
Let eqT_refl := (eqT_refl A n).
Local Hint Resolve eqT_refl : core.
Let eqp_refl := (eqp_refl _ _ _ _ _ _ _ _ _ cs).
Local Hint Resolve eqp_refl : core.
Let eqpP1 := (eqpP1 _ eqA n).
Local Hint Resolve eqpP1 : core.
Let eqP0 := (eqP0 _ eqA n).
Local Hint Resolve eqP0 : core.

Let eqTerm_minusTerm_plusTerm_invTerm := (eqTerm_minusTerm_plusTerm_invTerm _ _ _ _ _ _ _ _ _ cs n).
Local Hint Resolve eqTerm_minusTerm_plusTerm_invTerm : core.
Let mult_invTerm_com := (mult_invTerm_com _ _ _ _ _ _ _ _ _ cs n).
Local Hint Resolve mult_invTerm_com : core.
Let mult_invTerm_com_r := (mult_invTerm_com_r _ _ _ _ _ _ _ _ _ cs n).
Local Hint Resolve mult_invTerm_com_r : core.
Let canonicalpO := (canonicalpO A A0 eqA n ltM).
Local Hint Resolve canonicalpO : core.
Let canonicalp1 := (canonicalp1 A A0 eqA n ltM).
Local Hint Resolve canonicalp1 : core.
Let nZero_invTerm_nZero := (nZero_invTerm_nZero _ _ _ _ _ _ _ _ _ cs).
Hint Resolve nZero_invTerm_nZero : core.

Notation eqp_trans1 := (eqp_trans _ _ _ _ _ _ _ _ _ cs n) (only parsing).
Notation eqp_sym1 := (eqp_sym _ _ _ _ _ _ _ _ _ cs n) (only parsing).
Notation eqP1 := (eqP A eqA n) (only parsing).
Notation ltT1 := (ltT ltM) (only parsing).
Notation ltT_dec1 := (ltT_dec A n ltM ltM_dec) (only parsing).
Notation seqp_dec1 := (seqp_dec A A0 eqA eqA_dec n ltM) (only parsing).

Let eqp_refl1 := (eqp_refl n).
Hint Resolve eqp_refl1 : core.