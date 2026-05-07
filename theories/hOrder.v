(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Load hTerm.
Notation pOO := (pO A n) (only parsing).
Notation canonical1 := (canonical A0 eqA ltM) (only parsing).
Notation ltP1 := (ltP (A:=A) (n:=n) ltM) (only parsing).
Notation poly1 := (poly A0 eqA ltM) (only parsing).

Let ltP0 := (ltPO (A:=A) (n:=n) ltM).
Let ltP_hd := (ltP_hd (A:=A) (n:=n) (ltM:=ltM)).
Let ltP_tl := (ltP_tl (A:=A) (n:=n) (ltM:=ltM)). 
Let canonical0 := (canonical0 A A0 eqA n ltM).
Let canonical_cons := (canonical_cons _ _ _ _ _ _ _ _ _ cs eqA_dec).
Let canonical_nzeroP := (canonical_nzeroP _ _ _ _ _ _ _ _ _ cs eqA_dec).
Let canonical_imp_canonical := (canonical_imp_canonical _ _ _ _ _ _ _ _ _ cs eqA_dec).
Let canonical_pX_eqT := (canonical_pX_eqT _ _ _ _ _ _ _ _ _ cs).
Let canonical_skip_fst := (canonical_skip_fst _ _ _ _ _ _ _ _ _ cs eqA_dec).

Local Hint Resolve ltPO : core.
Local Hint Resolve ltP_hd : core.
Local Hint Resolve ltP_tl : core.
Local Hint Resolve canonical0 : core.
Local Hint Resolve canonical_cons : core.
