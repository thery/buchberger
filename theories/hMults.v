(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Load hPlus.
Notation mults1 := (mults (A:=A) multA (n:=n)) (only parsing).

Let canonical_mults := (canonical_mults _ _ _ _ _ _ _ _ _ cs eqA_dec _ _ ltM_dec os).
Local Hint Resolve canonical_mults : core.
Let mults_comp := (mults_comp _ _ _ _ _ _ _ _ _ cs n).
Local Hint Resolve mults_comp : core.
Let mults_com := (mults_com _ _ _ _ _ _ _ _ _ cs n).
Local Hint Resolve mults_com : core.
Let mults_multTerm := (mults_multTerm _ _ _ _ _ _ _ _ _ cs n).
Local Hint Resolve mults_multTerm : core.
Let mults_invTerm := (mults_invTerm _ _ _ _ _ _ _ _ _ cs eqA_dec n).
Local Hint Resolve mults_invTerm : core.
Let mults_dist1 := (mults_dist1 _ _ _ _ _ _ _ _ _ cs eqA_dec n).
Local Hint Resolve mults_dist1 : core.
Let mults_dist2 := (mults_dist2 _ _ _ _ _ _ _ _ _ cs eqA_dec n).
Local Hint Resolve mults_dist2 : core.
Let mults_dist_pluspf := (mults_dist_pluspf _ _ _ _ _ _ _ _ _ cs eqA_dec n).
Local Hint Resolve mults_dist_pluspf : core.
Let mults_T1 := (mults_T1 _ _ _ _ _ _ _ _ _ cs n).
Local Hint Resolve mults_T1 : core.
