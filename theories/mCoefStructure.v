(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)


Let eqA_ref := (eqA_ref _ _ _ _ _ _ _ _ _ cs).
Let plusA_eqA_comp :=  (plusA_eqA_comp _ _ _ _ _ _ _ _ _ cs).
Let multA_eqA_comp :=  (multA_eqA_comp _ _ _ _ _ _ _ _ _ cs).
Let invA_eqA_comp :=  (invA_eqA_comp _ _ _ _ _ _ _ _ _ cs).
Let divA_eqA_comp :=  (divA_eqA_comp _ _ _ _ _ _ _ _ _ cs).
Let plusA_A0 :=  (plusA_A0 _ _ _ _ _ _ _ _ _ cs).
Let plusA_com :=  (plusA_com _ _ _ _ _ _ _ _ _ cs).
Let multA_com :=  (multA_com _ _ _ _ _ _ _ _ _ cs).
Let invA_plusA :=  (invA_plusA _ _ _ _ _ _ _ _ _ cs).
Let plusA_assoc :=  (plusA_assoc _ _ _ _ _ _ _ _ _ cs).
Let multA_dist_l :=  (multA_dist_l _ _ _ _ _ _ _ _ _ cs).
Let multA_A0_l :=  (multA_A0_l _ _ _ _ _ _ _ _ _ cs).
Let multA_A1_l :=  (multA_A1_l _ _ _ _ _ _ _ _ _ cs).

Local Hint Resolve eqA_ref : core.
Local Hint Resolve plusA_eqA_comp  : core.
Local Hint Resolve multA_eqA_comp  : core.
Local Hint Resolve invA_eqA_comp  : core.
Local Hint Resolve divA_eqA_comp  : core.
Local Hint Resolve plusA_A0  : core.
Local Hint Resolve plusA_com  : core.
Local Hint Resolve multA_com  : core.
Local Hint Resolve invA_plusA  : core.
Local Hint Resolve plusA_assoc  : core.
Local Hint Resolve multA_dist_l  : core.
Local Hint Resolve multA_A0_l  : core.
Local Hint Resolve multA_A1_l  : core.
