(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)


Load hMults.

Notation minuspf1 :=
  (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec)
  (only parsing).
Notation divP1 := (divP A A0 eqA multA divA n) (only parsing).
Notation divTerm1 := (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n))
  (only parsing).
Notation ppc1 := (ppc (A:=A) A1 (n:=n)) (only parsing).

Definition minusP_is_plusP_mults := (minuspf_is_pluspf_mults _ _ _ _ _ _ _ _ _ cs).
Local Hint Resolve minusP_is_plusP_mults : core.
Definition canonical_minuspf := (canonical_minuspf _ _ _ _ _ _ _ _ _ cs).
Local Hint Resolve canonical_minuspf : core.
Definition minuspf_comp := (minuspf_comp _ _ _ _ _ _ _ _ _ cs).
Local Hint Resolve minuspf_comp : core.
Definition invTerm_T1_multTerm_T1 := (invTerm_T1_multTerm_T1 _ _ _ _ _ _ _ _ _ cs).
Local Hint Resolve invTerm_T1_multTerm_T1 : core.
Definition divTerm_nZ := (divTerm_nZ _ _ _ _ _ _ _ _ _ cs).
Local Hint Resolve divTerm_nZ : core.
Definition eqTerm_divTerm_comp := (eqTerm_divTerm_comp _ _ _ _ _ _ _ _ _ cs).
Local Hint Resolve eqTerm_divTerm_comp : core.
Definition ppc_com := (ppc_com _ _ _ _ _ _ _ _ _ cs).
Local Hint Resolve ppc_com : core.
Local Hint Resolve eqT_divTerm : core.
Definition divTerm_multTerm_l := (divTerm_multTerm_l _ _ _ _ _ _ _ _ _ cs).
Local Hint Resolve divTerm_multTerm_l : core.
Definition divTerm_multTerm_r := (divTerm_multTerm_r _ _ _ _ _ _ _ _ _ cs).
Local Hint Resolve divTerm_multTerm_r : core.
Definition div_is_T1 := (div_is_T1 _ _ _ _ _ _ _ _ _ cs).
Local Hint Resolve div_is_T1 : core.
Definition ppc_nZ := (ppc_nZ _ _ _ _ _ _ _ _ _ cs).
Local Hint Resolve ppc_nZ : core.
Definition divP_plusTerm := (divP_plusTerm _ _ _ _ _ _ _ _ _ cs).
Local Hint Resolve divP_plusTerm : core.
Definition divP_invTerm_l := (divP_invTerm_l _ _ _ _ _ _ _ _ _ cs).
Local Hint Resolve divP_invTerm_l : core.
Definition divP_invTerm_r := (divP_invTerm_r _ _ _ _ _ _ _ _ _ cs).
Local Hint Resolve divP_invTerm_r : core.
Definition divTerm_multTerml := (divTerm_multTerml _ _ _ _ _ _ _ _ _ cs).
Local Hint Resolve divTerm_multTerml : core.
Definition divTerm_multTermr := (divTerm_multTermr _ _ _ _ _ _ _ _ _ cs).
Local Hint Resolve divTerm_multTermr : core.
Definition divP_nZero := (divP_nZero _ _ _ _ _ _ _ _ _ cs).
Local Hint Resolve divP_nZero : core.
Definition divTerm_ppcr := (divTerm_ppcr _ _ _ _ _ _ _ _ _ cs).
Local Hint Resolve divTerm_ppcr : core.
Definition divTerm_ppcl := (divTerm_ppcl _ _ _ _ _ _ _ _ _ cs).
Local Hint Resolve divTerm_ppcl : core.
Definition divP_ppcl := (divP_ppcl _ _ _ _ _ _ _ _ _ cs).
Local Hint Resolve divP_ppcl : core.
Definition divP_ppclr := (divP_ppcr _ _ _ _ _ _ _ _ _ cs).
Local Hint Resolve divP_ppcr : core.
Definition divP_inv3 := (divP_inv3 _ _ _ _ _ _ _ _ _ cs).
Local Hint Resolve divP_inv3 : core.
