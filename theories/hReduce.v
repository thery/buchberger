(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Load hSpminus.

Notation reduce1 :=
  (reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec)
  (only parsing).
Notation inPolySet1 := (inPolySet A A0 eqA n ltM) (only parsing).
Notation pickinSetp1 := (pickinSetp A A0 eqA multA divA n ltM) (only parsing).
Notation irreducible1 :=
  (irreducible A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec)
  (only parsing).
Notation s2p1 := (s2p A A0 eqA n ltM) (only parsing).
Notation  ltp_eqp_comp  := (ltp_eqp_comp _ _ _ _ _ _ _ _ _ cs).


Let reducetop := (reducetop A A0 A1 eqA invA minusA multA divA eqA_dec n ltM
                ltM_dec).
Local Hint Resolve reducetop : core.
Let reduceskip := (reduceskip A A0 A1 eqA invA minusA multA divA eqA_dec n ltM
                ltM_dec).
Local Hint Resolve reduceskip : core.