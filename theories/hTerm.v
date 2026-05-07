(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Let eqTerm_refl := (eqTerm_refl _ _ _ _ _ _ _ _ _ cs n).
Local Hint Resolve eqTerm_refl : core.

Notation Term1 := (Term A n) (only parsing).
Notation eqTerm1 := (eqTerm (A:=A) eqA (n:=n)) (only parsing).
Notation zeroP1 := (zeroP (A:=A) A0 eqA (n:=n)) (only parsing).
Notation eqTerm_sym1 := (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n) (only parsing).
Notation eqTerm_trans1 := (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  (only parsing).
Notation eqTerm_dec1 := (eqTerm_dec _ _ eqA_dec n) (only parsing).
Notation zeroP_dec1 := (zeroP_dec A A0 eqA eqA_dec n) (only parsing).
Notation plusTerm1 := (plusTerm (A:=A) plusA (n:=n)) (only parsing).
Notation minusTerm1 := (minusTerm (A:=A) minusA (n:=n)) (only parsing).
Notation multTerm1 := (multTerm (A:=A) multA (n:=n)) (only parsing).
Notation invTerm1 := (invTerm (A:=A) invA (n:=n)) (only parsing).


Let multTerm_assoc := (multTerm_assoc _ _ _ _ _ _ _ _ _ cs).
Let multTerm_com := (multTerm_com _ _ _ _ _ _ _ _ _ cs).
Let eqTerm_plusTerm_comp := (eqTerm_plusTerm_comp _ _ _ _ _ _ _ _ _ cs).
Let eqTerm_multTerm_comp := (eqTerm_multTerm_comp _ _ _ _ _ _ _ _ _ cs).
Let eqTerm_invTerm_comp := (eqTerm_invTerm_comp _ _ _ _ _ _ _ _ _ cs).
Let T1_nz := (T1_nz _ _ _ _ _ _ _ _ _ cs n).
Let zeroP_multTerm_l := (zeroP_multTerm_l _ _ _ _ _ _ _ _ _ cs).
Let zeroP_multTerm_r := (zeroP_multTerm_r _ _ _ _ _ _ _ _ _ cs).
Let nzeroP_multTerm := (nzeroP_multTerm _ _ _ _ _ _ _ _ _ cs). 
Let T1_multTerm_l := (T1_multTerm_l _ _ _ _ _ _ _ _ _ cs n).
Let T1_multTerm_r:= (T1_multTerm_r _ _ _ _ _ _ _ _ _ cs n).
Let invTerm_invol := (invTerm_invol _ _ _ _ _ _ _ _ _ cs n).
Let zeroP_minusTerm := (zeroP_minusTerm _ _ _ _ _ _ _ _ _ cs n).

Local Hint Resolve multTerm_eqT invTerm_eqT : core.

Local Hint Resolve multTerm_assoc : core.
Local Hint Resolve multTerm_com : core.
Local Hint Resolve eqTerm_plusTerm_comp : core.
Local Hint Resolve eqTerm_multTerm_comp : core.
Local Hint Resolve eqTerm_invTerm_comp : core.
Local Hint Resolve T1_nz : core.
Local Hint Resolve nZero_invTerm_nZero : core.
Local Hint Resolve zeroP_multTerm_l : core.
Local Hint Resolve zeroP_multTerm_r : core.
Local Hint Resolve nzeroP_multTerm : core. 
Local Hint Resolve T1_multTerm_l : core.
Local Hint Resolve T1_multTerm_r : core.
Local Hint Resolve invTerm_invol : core.
Local Hint Resolve zeroP_minusTerm : core.

Local Hint Resolve multTerm_eqT invTerm_eqT : core.
