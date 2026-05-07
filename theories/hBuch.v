(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

 Load hBuchAux.

Notation unit1 := (unit A A0 A1 eqA divA n ltM) (only parsing).
Notation buch1 :=
  (buch A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os)
  (only parsing).
Notation stable1 := (stable A A0 eqA plusA multA eqA_dec n ltM ltM_dec)
  (only parsing).
Notation Cb := (Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec).
Notation poly := (poly A0 eqA ltM).
Notation addEnd := (addEnd A A0 eqA n ltM).
Notation zerop := (BuchAux.zerop A A0 eqA n ltM).
Notation foreigner := (foreigner A A0 A1 eqA multA n ltM).
Notation nf := (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os).
Notation reduce := (reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec).
Notation Grobner := (Grobner A A0 A1 eqA plusA invA minusA multA divA eqA_dec n ltM ltM_dec).
Notation s2p := (s2p A A0 eqA n ltM).
Notation mks := (mks A A0 eqA n ltM).
Notation divp := (divp A A0 eqA multA divA n ltM).
Notation reduceplus := (reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec).
Notation canonical := (canonical A0 eqA ltM).
Notation reducestar := (reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec).
Notation buch := (buch A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os).
Notation stable := (stable A A0 eqA plusA multA eqA_dec n ltM ltM_dec).