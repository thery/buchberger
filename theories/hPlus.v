(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Load hEq.

Notation pluspf1 :=
  (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec)
  (only parsing).
Let canonical_pluspf := (canonical_pluspf _ _ _ _ _ _ _ _ _ cs eqA_dec _ _ ltM_dec os).
Local Hint Resolve canonical_pluspf : core.
Let pluspf_assoc := (pluspf_assoc _ _ _ _ _ _ _ _ _ cs eqA_dec _ _ ltM_dec os).
Local Hint Resolve pluspf_assoc : core.
Let pluspf_com := (pluspf_com _ _ _ _ _ _ _ _ _ cs eqA_dec _ _ ltM_dec os).
Local Hint Resolve pluspf_com : core.
Let eqp_pluspf_com := (eqp_pluspf_com _ _ _ _ _ _ _ _ _ cs eqA_dec _ _ ltM_dec os).
Local Hint Resolve eqp_pluspf_com : core.
Let p0_pluspf_l := (p0_pluspf_l _ _ _ _ _ _ _ _ _ cs eqA_dec _ _ ltM_dec os).
Local Hint Resolve p0_pluspf_l : core.
Let p0_pluspf_r := (p0_pluspf_r _ _ _ _ _ _ _ _ _ cs eqA_dec _ _ ltM_dec os).
Local Hint Resolve p0_pluspf_r : core.
