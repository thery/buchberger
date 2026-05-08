(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

From Coq Require Export List.
From Coq Require Import Arith Inclusion Inverse_Image Wf_nat Relation_Definitions.
From Coq Require Import Relation_Operators Lexicographic_Product.
From Buchberger Require Import Relation_Operators_compat LetP.
From Buchberger Require Export WfR0.

Set Default Proof Using "Type".

Section Buch.
Load hCoefStructure.
Load hOrderStructure.
Load hWfRO.

Notation Cb := (Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec).
Notation poly := (poly A0 eqA ltM).

Inductive stable : list poly -> list poly -> Prop :=
    stable0 :
      forall P Q : list poly,
      (forall a : poly, Cb a P -> Cb a Q) ->
      (forall a : poly, Cb a Q -> Cb a P) -> 
      stable P Q.

Local Hint Resolve stable0 : core.
 
Theorem stable_refl : forall Q : list poly, stable Q Q.
Proof.
auto.
Qed.
 
Theorem stable_trans :
  forall Q y R : list poly, stable Q y -> stable y R -> stable Q R.
Proof.
intros Q y R H' H'0; inversion H'; inversion H'0; auto.
Qed.
 
Theorem stable_sym : forall Q R : list poly, stable R Q -> stable Q R.
Proof.
intros Q R H'; elim H'; auto.
Qed.

Let Cb_in := (Cb_in _ _ _ _ _ _ _ _ _ cs eqA_dec _ _ ltM_dec os).
Local Hint Resolve Cb_in : core.
Notation addEnd := (addEnd A A0 eqA n ltM).
Notation zerop := (BuchAux.zerop A A0 eqA n ltM).
Notation foreigner := (foreigner A A0 A1 eqA multA n ltM).
 
Theorem Cb_stable :
 forall (a : poly) (Q : list poly), Cb a Q -> stable Q (addEnd a Q).
Proof using os cs.
intros a Q H'0; apply stable0; auto.
intros a0 H'1.
apply Cb_trans with (b := a) (1 := cs); auto.
Qed.

Theorem in_incl :
 forall (A : Type) (p q : list A) (a b : A), incl p q -> In a p -> In a q.
Proof.
auto.
Qed.
 
Notation red := (red A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec).
Notation spolyp := (spolyp _ _ _ _ _ _ _ _ _ cs eqA_dec n ltM ltM_dec os).
Notation divp := (divp A A0 eqA multA divA n ltM).
Notation ppcp := (ppcp _ _ _ _ _ _ _ _ _ cs eqA_dec n ltM).

Inductive reds : poly -> poly -> list poly -> Prop :=
  | reds0 :
      forall (P : list poly) (a b : poly), red (spolyp a b) P -> reds a b P
  | reds1 :
      forall (P : list poly) (a b c : poly),
      In c P -> reds a c P -> reds c b P -> divp (ppcp a b) c -> reds a b P.
 
Theorem reds_com :
 forall (P : list poly) (a b : poly), reds a b P -> reds b a P.
Proof.
intros P a b H'; elim H'; simpl in |- *; auto.
intros P0 a0 b0 H'0.
apply reds0; auto.
apply red_com; auto.
intros P0 a0 b0 c H'0 H'1 H'2 H'3 H'4 H'5.
apply reds1 with (c := c); auto.
apply divp_ppc; auto.
Qed.

(* Now we are ready!! We start with the definition of genCpC *)
 
Inductive cpRes : Type :=
  | Keep : forall P : list poly, cpRes
  | DontKeep : forall P : list poly, cpRes.
 
Definition getRes : cpRes -> list poly.
intros H'; case H'; auto.
Defined.
 
Definition addRes : poly -> cpRes -> cpRes.
intros i H'; case H'.
intros H'0; exact (Keep (i :: H'0)).
intros H'0; exact (DontKeep (i :: H'0)).
Defined.

Notation divp_dec := (divp_dec _ _ _ _ _ _ _ _ _ cs eqA_dec n ltM).

Definition slice : poly -> poly -> list poly -> cpRes.
intros i a q; elim q; clear q.
case (foreigner_dec A A0 A1 eqA multA n ltM i a).
intros H; exact (DontKeep nil).
intros H; exact (Keep nil).
intros b q1 Rec.
case (divp_dec (ppcp i a) b).
intros divp10; exact (DontKeep (b :: q1)).
intros divp10.
case (divp_dec (ppcp i b) a).
intros divp11; exact Rec.
intros divp11; exact (addRes b Rec).
Defined.

Definition slicef : poly -> poly -> list poly -> list poly.
intros i a q; case (slice i a q); auto.
Defined.
 
Theorem slicef_incl :
 forall (a b : poly) (P : list poly), incl (slicef a b P) P.
Proof.
intros a b P; elim P; simpl in |- *; auto.
unfold slicef in |- *; simpl in |- *; auto.
case (foreigner_dec A A0 A1 eqA multA n ltM a b); intros H; apply incl_refl;
 auto with datatypes.
intros c; unfold slicef in |- *; simpl in |- *.
case (divp_dec (ppcp a b) c); auto with datatypes.
case (divp_dec (ppcp a c) b); auto with datatypes.
intros H' H'0 l; case (slice a b l); simpl in |- *; auto with datatypes.
Qed.

Theorem slice_inv :
 forall (a b : poly) (P : list poly) (c : poly),
 In c P ->
 In c (getRes (slice a b P)) \/ divp (ppcp a c) b.
Proof.
intros a b P; elim P; simpl in |- *; auto.
intros c H'; elim H'.
intros p aP1; case (divp_dec (ppcp a b) p); simpl in |- *; auto.
case (divp_dec (ppcp a p) b); auto.
intros H' H'0 H'1 c H'2; elim H'2;
 [ intros H'3; rewrite <- H'3; clear H'2 | intros H'3; clear H'2 ]; 
 auto.
case (slice a b aP1); simpl in |- *; auto.
intros P0 H' H'0 H'1 c H'2; elim H'2;
 [ intros H'3; rewrite <- H'3; clear H'2 | intros H'3; clear H'2 ]; 
 auto.
elim (H'1 c); [ intros H'5; try exact H'5 | intros H'5 | idtac ]; auto.
intros P0 H' H'0 H'1 c H'2; elim H'2;
 [ intros H'3; rewrite <- H'3; clear H'2 | intros H'3; clear H'2 ]; 
 auto.
elim (H'1 c); [ intros H'5; try exact H'5 | intros H'5 | idtac ]; auto.
Qed.

Theorem slice_cons :
 forall (i a : poly) (aP Q : list poly),
 slice i a aP = DontKeep Q ->
 (exists c : poly, In c Q /\ divp (ppcp i a) c) \/ foreigner i a.
Proof.
intros i a aP; elim aP.
simpl in |- *; case (foreigner_dec A A0 A1 eqA multA n ltM i a); auto.
intros H' Q H'0; inversion H'0.
intros a0 l H' Q; simpl in |- *.
case (divp_dec (ppcp i a) a0); auto.
intros H'0 H'1; inversion H'1; auto.
left; exists a0; split; simpl in |- *; auto.
case (divp_dec (ppcp i a0) a); auto.
generalize H'; clear H'; case (slice i a l); simpl in |- *; auto.
intros P H' H'0 H'1 H'2; inversion H'2.
intros P H' H'0 H'1 H'2; inversion H'2.
elim (H' P);
 [ intros H'5; elim H'5; intros c E; elim E; intros H'6 H'7; clear E H'5
 | intros H'5
 | idtac ]; auto.
left; exists c; split; simpl in |- *; auto.
Qed.

Definition Tl : list poly -> list poly -> Prop.
exact (fun x y : list poly => length x < length y).
Defined.
 
Theorem wf_Tl : well_founded Tl.
Proof.
apply (wf_inverse_image _ _ lt (length (A:= poly))); auto.
generalize lt_wf; auto.
Qed.

Scheme Sdep := Induction for prod Sort Prop.

Theorem slice_Tl :
 forall (a ia : poly) (L : list poly),
 Tl (slicef a ia L) (a :: L).
Proof.
intros a b P; elim P; simpl in |- *; auto.
unfold slicef in |- *; simpl in |- *; auto.
case (foreigner_dec A A0 A1 eqA multA n ltM a b); unfold Tl in |- *;
 simpl in |- *; auto.
intros c l.
unfold slicef in |- *; simpl in |- *; auto.
case (divp_dec (ppcp a b) c); auto.
unfold Tl in |- *; simpl in |- *; auto.
case (divp_dec (ppcp a c) b); auto.
intros H' H'0; case (slice a b l); simpl in |- *; auto.
unfold Tl in |- *; simpl in |- *; auto.
unfold Tl in |- *; simpl in |- *; auto.
unfold Tl in |- *; intros H' H'0; case (slice a b l); simpl in |- *;
 auto with arith.
Qed.

Inductive genPcP : poly -> list poly -> list poly -> list poly -> Prop :=
  | genPcP0 :
      forall (i : poly) (L : list poly),
      genPcP i nil L L
  | genPcP1 :
      forall (L L1 L2 L3 : list _) (a i : poly),
      slice i a L1 = Keep L2 ->
      genPcP i L2 L L3 ->
      genPcP i (a :: L1) L (addEnd (spolyp i a) L3)
  | genPcP2 :
      forall (L L1 L2 L3 : list _) (a i : poly),
      slice i a L1 = DontKeep L2 ->
      genPcP i L2 L L3 -> genPcP i (a :: L1) L L3.

Local Hint Resolve genPcP0 : core.

Theorem genPcP_spolyp1 :
 forall (i : poly) (L L1 L2 : list _),
 genPcP i L1 L L2 ->
 forall a : poly,
 In a L2 ->
 (exists b : poly, In b L1 /\ a = spolyp i b) \/ In a L.
Proof.
intros i L L1 L2 H'; elim H'; clear H'; simpl in |- *; auto.
intros L0 L3 L4 L5 a i0 H' H'0 H'1 a0 H'2.
case (addEnd_cons A A0 eqA n ltM) with (1 := H'2); auto; intros H'7.
rewrite H'7; auto.
left; exists a; split; simpl in |- *; auto.
elim (H'1 a0); auto.
intros H'3; case H'3; intros b E; case E; intros H'4 H'5; rewrite H'5;
 clear E H'3.
left; exists b; split; auto.
right; try assumption.
generalize (slicef_incl i0 a L3); unfold slicef in |- *; rewrite H'; auto.
intros L0 L3 L4 L5 a i0 H' H'0 H'1 a0 H'2.
elim (H'1 a0);
 [ intros H'5; elim H'5; intros b E; elim E; intros H'6 H'7; rewrite H'7;
    clear E H'5
 | intros H'5
 | idtac ]; auto.
left; exists b; split; [ right | idtac ]; auto.
generalize (slicef_incl i0 a L3); unfold slicef in |- *; rewrite H'; auto.
Qed.

Let addEnd_id1 := (addEnd_id1 A A0 eqA n ltM).
Let addEnd_id2 := (addEnd_id2 A A0 eqA n ltM).
Local Hint Resolve addEnd_id2 : core.
Local Hint Resolve addEnd_id1 : core.
 
Theorem genPcP_incl :
 forall (i : poly) (L L1 L2 : list _), genPcP i L1 L L2 -> incl L L2.
Proof.
intros i L L1 L2 H'; elim H'; simpl in |- *; auto with datatypes.
intros L0 L3 L4 L5 a i0 H'0 H'1 H'2.
unfold incl in |- *; simpl in |- *; auto.
Qed.
 
Lemma spolyp_cons_genPcP0 :
 forall (aP R Q : list _) (i : poly),
 genPcP i aP R Q -> ~ zerop i ->
 forall b : poly, In b aP -> ~ zerop b ->
 exists c : poly,
   In c aP /\
   (In (spolyp i c) Q \/ foreigner i c) /\ divp (ppcp i b) c.
Proof.
intros aP R Q i H'; elim H'; clear H' i aP R Q; simpl in |- *; auto.
intros i L H' b H'0; elim H'0.
intros L L1 L2 L3 a i H' H'0 H'1 H'2 b H'3 H'4.
cut (incl L2 L1);
 [ intros incl0
 | generalize (slicef_incl i a L1); unfold slicef in |- *; rewrite H' ]; 
 auto.
elim H'3; [ intros H'5; rewrite <- H'5; clear H'3 | intros H'5; clear H'3 ];
 auto.
exists a; split; [ idtac | split; [ left | idtac ] ]; auto.
rewrite H'5; auto.
apply zerop_ddivp_ppc; auto.
elim (slice_inv i a L1 b); [ intros H'10 | intros H'10 | idtac ]; auto.
rewrite H' in H'10; simpl in H'10; auto.
lapply H'1;
 [ intros H'3; elim (H'3 b);
    [ intros c E; elim E; intros H'9 H'11; elim H'11; intros H'12 H'13;
       elim H'12;
       [ intros H'14; clear H'12 H'11 E H'1
       | intros H'14; clear H'12 H'11 E H'1 ]
    | clear H'1
    | clear H'1 ]
 | clear H'1 ]; auto.
exists c; split; [ right | idtac ]; auto.
exists c; split; [ idtac | split; [ right | idtac ] ]; auto.
exists a; split; [ idtac | split ]; auto.
intros L L1 L2 L3 a i H' H'0 H'1 H'2 b H'3 H'4.
cut (incl L2 L1);
 [ intros incl0
 | generalize (slicef_incl i a L1); unfold slicef in |- *; rewrite H' ]; 
 auto.
elim H'3; [ intros H'5; rewrite <- H'5; clear H'3 | intros H'5; clear H'3 ];
 auto.
elim (slice_cons i a L1 L2);
 [ intros H'8; elim H'8; intros c E; elim E; intros H'9 H'10; clear E H'8
 | intros H'8
 | idtac ]; auto.
lapply H'1;
 [ intros H'3; elim (H'3 c);
    [ intros c0 E; elim E; intros H'11 H'12; elim H'12; intros H'13 H'14;
       elim H'13;
       [ intros H'15; clear H'13 H'12 E H'1
       | intros H'15; clear H'13 H'12 E H'1 ]
    | clear H'1
    | clear H'1 ]
 | clear H'1 ]; auto.
exists c0; split; [ idtac | split; [ left | idtac ] ]; auto.
apply (divp_trans _ _ _ _ _ _ _ _ _ cs n ltM) with (y := ppcp i c); auto.
apply divP_ppc; auto.
apply divp_ppc; auto.
apply zerop_ddivp_ppc; auto.
rewrite H'5; auto.
exists c0; split; [ idtac | split; [ right | idtac ] ]; auto.
apply (divp_trans _ _ _ _ _ _ _ _ _ cs n ltM) with (y := ppcp i c); auto.
rewrite H'5; auto.
apply divP_ppc; auto.
apply divp_ppc; auto.
apply zerop_ddivp_ppc; auto.
rewrite <- H'5; auto.
apply divp_nzeropr with (1 := H'10); auto.
exists a; split; [ idtac | split; [ right | idtac ] ]; auto.
rewrite H'5; auto.
apply zerop_ddivp_ppc; auto.
elim (slice_inv i a L1 b); [ intros H'10 | intros H'10 | idtac ]; auto.
rewrite H' in H'10; simpl in H'10; auto.
lapply H'1;
 [ intros H'3; elim (H'3 b);
    [ intros c E; elim E; intros H'9 H'11; elim H'11; intros H'12 H'13;
       elim H'12;
       [ intros H'14; clear H'12 H'11 E H'1
       | intros H'14; clear H'12 H'11 E H'1 ]
    | clear H'1
    | clear H'1 ]
 | clear H'1 ]; auto.
exists c; split; [ right | idtac ]; auto.
exists c; split; [ idtac | split; [ right | idtac ] ]; auto.
elim (slice_cons i a L1 L2);
 [ intros H'8; elim H'8; intros c E; elim E; intros H'9 H'11; clear E H'8
 | intros H'8
 | idtac ]; auto.
lapply H'1;
 [ intros H'3; elim (H'3 c);
    [ intros c0 E; elim E; intros H'12 H'13; elim H'13; intros H'14 H'15;
       elim H'14;
       [ intros H'16; clear H'14 H'13 E H'1
       | intros H'16; clear H'14 H'13 E H'1 ]
    | clear H'1
    | clear H'1 ]
 | clear H'1 ]; auto.
exists c0; split; [ idtac | split; [ left | idtac ] ]; auto.
apply (divp_trans _ _ _ _ _ _ _ _ _ cs n ltM) with (y := ppcp i c); auto.
apply (divp_trans _ _ _ _ _ _ _ _ _ cs n ltM) with (y := ppcp i a); auto.
apply divP_ppc; auto.
apply divp_ppc; auto.
apply zerop_ddivp_ppc; auto.
apply divP_ppc; auto.
apply divp_ppc; auto.
apply zerop_ddivp_ppc; auto.
apply divp_nzeropr with (1 := H'10); auto.
exists c0; split; [ idtac | split; [ right | idtac ] ]; auto.
apply (divp_trans _ _ _ _ _ _ _ _ _ cs n ltM) with (y := ppcp i a); auto.
apply divP_ppc; auto.
apply divp_ppc; auto.
apply zerop_ddivp_ppc; auto.
apply (divp_trans _ _ _ _ _ _ _ _ _ cs n ltM) with (y := ppcp i c); auto.
apply divP_ppc; auto.
apply divp_ppc; auto.
apply zerop_ddivp_ppc; auto.
apply divp_nzeropr with (1 := H'10); auto.
apply divp_nzeropr with (1 := H'11); auto.
exists a; split; [ idtac | split; [ right | idtac ] ]; auto.
Qed.

Lemma spolyp_cons_genPcP :
 forall (aP R Q : list _) (i : poly),
 genPcP i aP R Q -> ~ zerop i ->
 forall b : poly,
 In b aP -> ~ zerop b ->
 exists c : poly,
   In c aP /\
   (In (spolyp i c) Q \/ red (spolyp i c) (addEnd i aP)) /\
   divp (ppcp i b) c.
Proof.
intros aP R Q i H' H'0 b H'1 H'2.
lapply (spolyp_cons_genPcP0 aP R Q i);
 [ intros H'7; lapply H'7;
    [ intros H'8; elim (H'8 b);
       [ intros c E; elim E; intros H'12 H'13; elim H'13; intros H'14 H'15;
          elim H'14;
          [ intros H'16; clear H'14 H'13 E H'7
          | intros H'16; clear H'14 H'13 E H'7 ]
       | clear H'7
       | clear H'7 ]
    | clear H'7 ]
 | idtac ]; auto.
exists c; split; [ idtac | split; [ left | idtac ] ]; auto.
exists c; split; [ idtac | split; [ right | idtac ] ]; auto.
apply foreigner_red; auto.
Qed.

Theorem Cb_genPcP :
 forall (i : poly) (P Q R S : list poly),
 genPcP i P R Q -> Cb i S ->
 (forall a : poly, In a P -> Cb a S) ->
 (forall a : poly, In a R -> Cb a S) ->
 forall a : poly, In a Q -> Cb a S.
Proof.
intros i P Q R S H'; elim H'; simpl in |- *; auto.
intros L L1 L2 L3 a i0 H'0 H'1 H'2 H'3 H'4 H'5 a0 H'6.
case (addEnd_cons A A0 eqA n ltM) with (1 := H'6); auto; intros H'7.
rewrite H'7; auto.
apply Cb_sp; auto.
apply H'2; auto.
intros a1 H'8.
apply H'4; auto.
right.
generalize (slicef_incl i0 a L1); unfold slicef in |- *; rewrite H'0; auto.
intros L L1 L2 L3 a i0 H'0 H'1 H'2 H'3 H'4 H'5 a0 H'6; auto.
apply H'2; auto.
intros a1 H'7.
apply H'4; auto.
generalize (slicef_incl i0 a L1); unfold slicef in |- *; rewrite H'0; auto.
Qed.

Definition genPcPf0 :
  forall (i : poly) (aP R : list poly),
  {Q : list poly | genPcP i aP R Q}.
intros i aP; pattern aP in |- *.
apply well_founded_induction_type with (A := list poly) (R := Tl);
 clear aP; auto.
try exact wf_Tl.
intros aP; case aP.
intros H' R; exists R; auto.
intros a L1 Rec L; generalize (@refl_equal _ (slice i a L1));
 pattern (slice i a L1) at 2 in |- *; case (slice i a L1).
intros L2 H'.
lapply (Rec L2); [ intros H'1; elim (H'1 L); intros L3 E | idtac ]; auto.
exists (addEnd (spolyp i a) L3); auto.
apply genPcP1 with (L2 := L2); auto.
generalize (slice_Tl i a L1); unfold slicef in |- *; rewrite H';
 simpl in |- *; auto.
intros L2 H'.
lapply (Rec L2); [ intros H'1; elim (H'1 L); intros L3 E | idtac ]; auto.
exists L3; auto.
apply genPcP2 with (L2 := L2); auto.
generalize (slice_Tl i a L1); unfold slicef in |- *; rewrite H';
 simpl in |- *; auto.
Defined.

Definition genPcPf : poly -> list poly -> list poly -> list poly.
intros i aP Q; case (genPcPf0 i aP Q).
intros x H'; exact x.
Defined.

(* The proof will carry on if we have the following 3 properties for
   the function genPcPf *)

Theorem Cb_genPcPf :
 forall (b : poly) (P Q R : list poly), Cb b R ->
 (forall a : poly, In a P -> Cb a R) ->
 (forall a : poly, In a Q -> Cb a R) ->
 forall a : poly, In a (genPcPf b P Q) -> Cb a R.
Proof.
intros b P Q R; unfold genPcPf in |- *; case (genPcPf0 b P Q).
intros x H' H'0 H'1 H'2 a H'3.
apply Cb_genPcP with (i := b) (P := P) (Q := x) (R := Q); auto.
Qed.
 
Theorem genPcPf_incl :
 forall (a : poly) (aL Q : list poly), incl Q (genPcPf a aL Q).
Proof.
intros a aL Q; unfold genPcPf in |- *; case (genPcPf0 a aL Q).
intros x H'.
apply genPcP_incl with (i := a) (L1 := aL); auto.
Qed.

Local Hint Resolve genPcPf_incl : core.

Theorem spolyp_addEnd_genPcPf :
 forall (aP R Q : list poly) (a b : poly),
 ~ zerop a -> ~ zerop b -> In b aP ->
 exists c : poly,
   In c aP /\
   (In (spolyp a c) (genPcPf a aP Q) \/ red (spolyp a c) (addEnd a aP)) /\
   divp (ppcp a b) c.
Proof.
intros aP H' Q a b H'0 H'1 H'2.
unfold genPcPf in |- *.
case (genPcPf0 a aP Q).
intros x H'3.
apply spolyp_cons_genPcP with (R := Q); auto.
Qed.

(* Now we can define the optimized version of Buchberger *)
 
Definition genOCPf : list poly -> list poly.
intros H'; elim H'.
exact (nil (A:=poly)).
intros a l rec; exact (genPcPf a l rec).
Defined.

(* Now we can define the optimized version of Buchberger *)
 
Theorem genOCPf_stable :
 forall (a : poly) (P : list poly), In a (genOCPf P) -> Cb a P.
Proof.
intros a P; generalize a; elim P; clear a P; simpl in |- *; auto.
intros a H; elim H.
intros a l H' a0 H'0.
apply Cb_genPcPf with (b := a) (P := l) (Q := genOCPf l); auto with datatypes.
apply Cb_id with (1 := cs); auto with datatypes.
intros; apply Cb_in1 with (1 := cs); auto.
apply Cb_id with (1 := cs); auto with datatypes.
intros; apply Cb_in1 with (1 := cs); auto.
Qed.
 
Notation nf := (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os).

Inductive OBuch : list poly -> list poly -> list poly -> Prop :=
  | OBuch0 : forall aL : list poly, OBuch aL nil aL
  | OBuch1 :
      forall (a : poly) (aP Q R : list poly),
      OBuch (addEnd (nf a aP) aP) (genPcPf (nf a aP) aP Q) R ->
      ~ zerop (nf  a aP) -> OBuch aP (a :: Q) R
  | OBuch2 :
      forall (a : poly) (aP Q R : list poly),
      OBuch aP Q R -> zerop (nf a aP) -> OBuch aP (a :: Q) R.

Local Hint Resolve OBuch0 OBuch2 : core.
Local Hint Resolve incl_refl incl_tl : core.
 
Theorem incl_addEnd1 :
 forall (a : poly) (L1 L2 : list poly),
 incl (addEnd a L1) L2 -> incl (a :: L1) L2.
Proof.
unfold incl in |- *; simpl in |- *; auto.
intros a L1 L2 H' a0 H'0; case H'0;
 [ intros H'1; rewrite <- H'1; clear H'0 | intros H'1; clear H'0 ]; 
 auto.
Qed.
 
Theorem ObuchPincl :
 forall aP R Q : list poly, OBuch aP Q R -> incl aP R.
Proof.
intros aP R Q H'; elim H'; simpl in |- *; auto.
intros a aP0 Q0 R0 H'0 H'1 H'2; try assumption.
apply incl_tran with (m := nf a aP0 :: aP0); simpl in |- *; 
 auto.
apply incl_addEnd1; auto.
Qed.
 
Theorem ObuchPred :
 forall aP R Q : list poly,
 OBuch aP Q R -> forall a : poly, In a aP -> red a R.
Proof.
intros aP R Q H'; elim H'; simpl in |- *; auto.
intros; apply red_cons with (1 := cs); auto.
Qed.
 
Theorem ObuchQred :
 forall aP R Q : list poly,
 OBuch aP Q R -> forall a : poly, In a Q -> red a R.
Proof.
intros aP R Q H'; elim H'; simpl in |- *; auto.
intros aL a H'0; elim H'0.
intros a aP0 Q0 R0 H'0 H'1 H'2 a0 H'3; elim H'3;
 [ intros H'4; rewrite <- H'4; clear H'3 | intros H'4; clear H'3 ]; 
 auto.
apply red_incl with (1 := cs) (p := addEnd (nf a aP0) aP0); auto.
apply ObuchPincl with (Q := genPcPf (nf a aP0) aP0 Q0); auto.
apply nf_red with (cs := cs) (os := os) (aP := aP0); simpl in |- *; auto.
unfold incl in |- *; auto.
apply red_cons with (1 := cs); auto.
apply H'1; auto.
apply (genPcPf_incl (nf a aP0) aP0 Q0); auto.
intros a aP0 Q0 R0 H'0 H'1 H'2 a0 H'3; elim H'3;
 [ intros H'4; rewrite <- H'4; clear H'3 | intros H'4; clear H'3 ]; 
 auto.
apply red_incl with (1 := cs) (p := aP0); auto.
apply ObuchPincl with (Q := Q0); auto.
apply zerop_red with (cs := cs) (os := os); auto.
Qed.

Theorem OBuch_Stable :
 forall P Q R : list poly,
 OBuch P Q R -> (forall a : poly, In a Q -> Cb a P) -> stable P R.
Proof.
intros P Q R H'; elim H'; simpl in |- *; auto.
intros a aP Q0 R0 H'0 H'1 H'2 H'3.
apply stable_trans with (y := addEnd (nf a aP) aP); auto.
apply stable0; auto.
intros a0 H'4.
apply Cb_trans with (1 := cs) (b := nf a aP); auto.
apply nf_Cb; auto.
apply H'1; auto.
intros a0 H'4.
apply Cb_genPcPf with (b := nf a aP) (P := aP) (Q := Q0); auto.
apply Cb_id with (1 := cs); auto.
intros; apply Cb_in; auto.
apply Cb_id with (1 := cs); auto.
Qed.

Inductive redIn : poly -> poly -> list poly -> list poly -> list poly -> Prop :=
  | redIn0b :
      forall (P Q R : list poly) (a b : poly),
      redIn b a P Q R -> redIn a b P Q R
  | redIn0 :
      forall (P Q R : list poly) (a b : poly),
      In (spolyp a b) Q -> redIn a b P Q R
  | redIn1 :
      forall (P Q R : list poly) (a b : poly),
      red  (spolyp a b) R -> redIn a b P Q R
  | redIn2 :
      forall (P Q R : list poly) (a b c : poly),
      In c P -> redIn a c P Q R -> redIn b c P Q R -> divp (ppcp a b) c ->
      redIn a b P Q R.

Local Hint Resolve redIn1 redIn0 : core.

Remark lem_redIn_nil :
 forall (aP Q R : list poly) (a b : poly),
 In a R -> In b R -> redIn a b aP Q R -> Q = nil -> aP = R -> reds a b R.
Proof.
intros aP Q R a b H' H'0 H'1; elim H'1; auto.
intros P Q0 R0 a0 b0 H'2 H'3 H'4 H'5.
apply reds_com; auto.
intros P Q0 R0 a0 b0 H'2 H'3 H'4.
rewrite H'3 in H'2; elim H'2.
intros P Q0 R0 a0 b0 H'2 H'3 H'4; rewrite <- H'4.
rewrite H'4.
apply reds0; auto.
intros P Q0 R0 a0 b0 c H'2 H'3 H'4 H'5 H'6 H'7 H'8 H'9.
apply reds1 with (c := c); auto.
rewrite <- H'9; auto.
apply reds_com; auto.
Qed.

Theorem redIn_nil :
 forall (R : list poly) (a b : poly),
 In a R -> In b R -> redIn a b R nil R -> reds a b R.
Proof.
intros R a b H' H'0 H'1.
apply lem_redIn_nil with (aP := R) (Q := nil (A:=poly)); auto.
Qed.

Remark lem_redln_cons :
 forall (aP R Q : list poly) (a b : poly),
 In a aP ->
 In b aP ->
 redIn a b aP Q R ->
 forall (c : poly) (Q1 : list poly),
 Q = c :: Q1 -> red c R -> redIn a b aP Q1 R.
Proof.
intros aP R Q a b H' H'0 H'1; elim H'1; auto.
intros P Q0 R0 a0 b0 H'2 H'3 c Q1 H'4 H'5.
apply redIn0b; auto.
apply H'3 with (c := c); auto.
intros P Q0 R0 a0 b0 H'2 c Q1 H'3 H'4.
rewrite H'3 in H'2; elim H'2; auto.
intros H'5; rewrite H'5 in H'4; auto.
intros P Q0 R0 a0 b0 c H'2 H'3 H'4 H'5 H'6 H'7 c0 Q1 H'8 H'9.
apply redIn2 with (c := c); auto.
apply (H'4 c0); auto.
apply (H'6 c0); auto.
Qed.
 
Theorem redln_cons :
 forall (aP R Q : list poly) (a b c : poly),
 In a aP -> In b aP ->
 redIn a b aP (c :: Q) R -> red c R -> redIn a b aP Q R.
Proof.
intros aP R Q a b c H' H'0 H'1 H'2; try assumption.
apply lem_redln_cons with (Q := c :: Q) (c := c); auto.
Qed.

Theorem redInclP :
 forall (P Q R : list poly) (a b : poly),
 redIn a b P Q R ->
 forall P1 : list poly, incl P P1 -> redIn a b P1 Q R.
Proof.
intros P Q R a b H'; elim H'; auto.
intros P0 Q0 R0 a0 b0 H'0 H'1 P1 H'2.
apply redIn0b; auto.
intros P0 Q0 R0 a0 b0 c H'0 H'1 H'2 H'3 H'4 H'5 Q1 H'6.
apply redIn2 with (c := c); auto.
Qed.
 
Theorem redInInclQ :
 forall (P Q R : list poly) (a b : poly),
 redIn a b P Q R ->
 forall Q1 : list poly, incl Q Q1 -> redIn a b P Q1 R.
Proof.
intros P Q R a b H'; elim H'; auto.
intros P0 Q0 R0 a0 b0 H'0 H'1 Q1 H'2; try assumption.
apply redIn0b; auto.
intros P0 Q0 R0 a0 b0 c H'0 H'1 H'2 H'3 H'4 H'5 Q1 H'6; try assumption.
apply redIn2 with (c := c); auto.
Qed.
 
Theorem redInclR :
 forall (P Q R : list poly) (a b : poly),
 redIn a b P Q R ->
 forall R1 : list poly, incl R R1 -> redIn a b P Q R1.
Proof.
intros P Q R a b H'; elim H'; simpl in |- *; auto.
intros P0 Q0 R0 a0 b0 H'0 H'1 R1 H'2; try assumption.
apply redIn0b; auto.
intros P0 Q0 R0 a0 b0 H'0 R1 H'1; try assumption.
apply redIn1; auto.
apply red_incl with (1 := cs) (p := R0); auto.
intros P0 Q0 R0 a0 b0 c H'0 H'1 H'2 H'3 H'4 H'5 R1 H'6.
apply redIn2 with (c := c); auto.
Qed.

Remark lem_redln_cons_gen :
 forall (aP R Q : list poly) (a b : poly),
 In a aP ->
 In b aP ->
 redIn a b aP Q R ->
 forall (c : poly) (Q1 : list poly),
 incl (addEnd (nf c aP) aP) R ->
 Q = c :: Q1 -> redIn a b (addEnd (nf c aP) aP) Q1 R.
Proof.
intros aP R Q a b H' H'0 H'1; elim H'1; auto.
intros P Q0 R0 a0 b0 H'2 H'3 c Q1 H'4 H'5.
apply redIn0b; auto.
intros P Q0 R0 a0 b0 H'2 c Q1 H'3 H'4.
rewrite H'4 in H'2; elim H'2; auto.
intros H'5; rewrite H'5.
apply redIn1; auto.
apply nf_red with (aP := P) (cs := cs) (os := os); auto.
apply incl_tran with (m := nf c P :: P); simpl in |- *; auto.
apply incl_addEnd1; auto.
apply red_cons with (1 := cs); auto.
apply in_incl with (p := nf c P :: P); auto.
apply incl_addEnd1; auto.
rewrite H'5; simpl in |- *; auto.
intros P Q0 R0 a0 b0 c H'2 H'3 H'4 H'5 H'6 H'7 c0 Q1 H'8 H'9.
apply redIn2 with (c := c); auto.
Qed.

Theorem redln_cons_gen :
 forall (aP R Q : list poly) (a b c : poly),
 In a aP ->
 In b aP ->
 redIn a b aP (c :: Q) R ->
 incl (addEnd (nf c aP) aP) R ->
 redIn a b (addEnd (nf c aP) aP) Q R.
Proof.
intros aP R Q a b c H' H'0 H'1 H'2.
apply lem_redln_cons_gen with (Q := c :: Q); auto.
Qed.

Local Hint Resolve redln_cons_gen : core.

Theorem red_gen_in :
 forall (a : poly) (aP R Q : list poly),
 ~ zerop (nf a aP) ->
 OBuch (addEnd (nf a aP) aP) (genPcPf (nf a aP) aP Q) R ->
 (forall b c : poly, In b aP -> In c aP -> redIn b c aP (a :: Q) R) ->
 forall b : poly,
 In b aP -> ~ zerop b ->
 redIn (nf a aP) b (addEnd (nf a aP) aP) (genPcPf (nf a aP) aP Q) R.
Proof.
intros a aP R Q H' H'0 H'1 b H'2 H'3.
lapply (spolyp_addEnd_genPcPf aP);
 [ intros H'5;
    elim (H'5 Q (nf a aP) b);
    [ intros c E; elim E; intros H'12 H'13; elim H'13; intros H'14 H'15;
       elim H'14;
       [ intros H'16; clear H'14 H'13 E | intros H'16; clear H'14 H'13 E ]
    | idtac
    | idtac
    | idtac ]
 | idtac ]; auto.
apply redIn2 with (c := c); simpl in |- *; auto.
apply redln_cons_gen; auto.
apply redInInclQ with (Q := a :: Q); auto with datatypes.
apply ObuchPincl with (Q := genPcPf (nf a aP) aP Q); auto.
apply redIn2 with (c := c); simpl in |- *; auto.
apply redIn1.
apply red_incl with (p := addEnd (nf a aP) aP) (1 := cs); auto.
apply ObuchPincl with (Q := genPcPf (nf a aP) aP Q); auto.
apply redln_cons_gen; auto.
apply redInInclQ with (Q := a :: Q); auto with datatypes.
apply ObuchPincl with (Q := genPcPf (nf a aP) aP Q); auto.
Qed.

Theorem OBuch_Inv :
 forall aP R Q : list poly,
 OBuch aP Q R ->
 (forall a b : poly, In a aP -> In b aP -> redIn a b aP Q R) ->
 forall a b : poly, In a R -> In b R -> reds a b R.
Proof.
intros aP R Q H'; elim H'; simpl in |- *; auto.
intros aL H'0 a b H'1 H'2; try assumption.
apply redIn_nil; auto.
intros a aP0 Q0 R0 H'0 H'1 H'2 H'3 a0 b H'4 H'5.
apply H'1; auto.
intros a1 b0 H'6.
case (addEnd_cons A A0 eqA n ltM) with (1 := H'6); auto.
intros H'7; rewrite <- H'7; auto.
intros H'8.
case (addEnd_cons A A0 eqA n ltM) with (1 := H'8); auto.
intros H'9; rewrite <- H'9; auto.
apply redIn1; auto.
apply red_id; auto.
intros H'9.
case (zerop_dec A A0 eqA n ltM b0); intros Z; auto.
apply redIn1; auto.
apply zerop_red_spoly_r; auto.
rewrite H'7; auto.
apply red_gen_in; auto.
intros H'7 H'8.
case (addEnd_cons A A0 eqA n ltM) with (1 := H'8); auto.
intros H'9; rewrite <- H'9; auto.
apply redIn0b.
case (zerop_dec A A0 eqA n ltM a1); intros Z.
apply redIn1; auto.
apply zerop_red_spoly_r; auto.
rewrite H'9.
apply red_gen_in; auto.
intros H'9.
apply redln_cons with (c := a); simpl in |- *; auto.
apply redInclP with (P := aP0); auto.
apply redInInclQ with (Q := a :: Q0); auto with datatypes.
unfold incl in |- *; auto.
apply nf_red with (aP := aP0) (cs := cs) (os := os); auto.
apply incl_tran with (m := addEnd(nf  a aP0) aP0); auto.
unfold incl in |- *; auto.
apply ObuchPincl with (Q := genPcPf (nf a aP0) aP0 Q0); auto.
apply red_cons with (1 := cs); auto.
apply in_incl with (p := addEnd (nf a aP0) aP0); simpl in |- *; auto.
apply ObuchPincl with (Q := genPcPf (nf a aP0) aP0 Q0); auto.
intros a aP0 Q0 R0 H'0 H'1 H'2 H'3 a0 b H'4 H'5.
apply H'1; auto.
intros a1 b0 H'6 H'7.
apply redln_cons with (c := a); auto.
apply red_incl with (p := aP0) (1 := cs); auto.
apply ObuchPincl with (Q := Q0); auto.
apply zerop_red with (cs := cs) (os := os); auto.
Qed.

Theorem addEnd_incl :
 forall (a : poly) (L1 L2 : list poly),
 incl (a :: L1) L2 -> incl (addEnd a L1) L2.
Proof.
unfold incl in |- *; simpl in |- *; auto.
intros a L1 L2 H' a0 H'0.
case addEnd_cons with (1 := H'0); auto.
Qed.

Theorem genOCp_redln :
 forall aL1 R : list poly,
 incl aL1 R ->
 forall a b : poly,
 In a aL1 -> In b aL1 -> redIn a b aL1 (genOCPf aL1) R.
Proof.
intros aL1; elim aL1; simpl in |- *; auto.
intros a l H' R H'0 a0 b H'1 H'2.
elim H'2; [ intros H'3; rewrite <- H'3; clear H'2 | intros H'3; clear H'2 ];
 auto.
elim H'1; [ intros H'2; rewrite <- H'2; clear H'1 | intros H'2; clear H'1 ];
 auto.
apply redIn1; auto.
apply red_id; auto.
apply redIn0b.
case (zerop_dec A A0 eqA n ltM a); intros Z; auto.
apply redIn1; auto.
apply zerop_red_spoly_l; auto.
case (zerop_dec A A0 eqA n ltM a0); intros Z1; auto.
apply redIn1; auto.
apply zerop_red_spoly_r; auto.
lapply (spolyp_addEnd_genPcPf l);
 [ intros H'4; elim (H'4 (genOCPf l) a a0);
    [ intros c E; elim E; intros H'11 H'12; elim H'12; intros H'13 H'14;
       elim H'13;
       [ intros H'15; clear H'13 H'12 E | intros H'15; clear H'13 H'12 E ]
    | idtac
    | idtac
    | idtac ]
 | idtac ]; auto.
apply redIn2 with (c := c); auto.
simpl in |- *; auto.
apply redInInclQ with (Q := genOCPf l); auto.
apply redInclP with (P := l); auto.
apply H'; auto.
apply incl_tran with (m := a :: l); simpl in |- *; auto.
apply redIn2 with (c := c); auto.
simpl in |- *; auto.
apply redIn1; auto.
apply red_incl with (p := addEnd a l) (1 := cs); auto.
apply addEnd_incl; auto.
apply redInclP with (P := l); auto.
apply redInInclQ with (Q := genOCPf l); auto.
apply H'; auto.
apply incl_tran with (m := a :: l); auto.
elim H'1; [ intros H'2; rewrite <- H'2; clear H'1 | intros H'2; clear H'1 ];
 auto.
case (zerop_dec A A0 eqA n ltM a); intros Z; auto.
apply redIn1; auto.
apply zerop_red_spoly_l; auto.
case (zerop_dec A A0 eqA n ltM b); intros Z1; auto.
apply redIn1; auto.
apply zerop_red_spoly_r; auto.
lapply (spolyp_addEnd_genPcPf l);
 [ intros H'4; elim (H'4 (genOCPf l) a b);
    [ intros c E; elim E; intros H'11 H'12; elim H'12; intros H'13 H'14;
       elim H'13;
       [ intros H'15; clear H'13 H'12 E | intros H'15; clear H'13 H'12 E ]
    | idtac
    | idtac
    | idtac ]
 | idtac ]; auto.
apply redIn2 with (c := c); simpl in |- *; auto.
apply redInInclQ with (Q := genOCPf l); auto.
apply redInclP with (P := l); auto.
apply H'; auto.
apply incl_tran with (m := a :: l); simpl in |- *; auto.
apply redIn2 with (c := c); simpl in |- *; auto.
apply redIn1; auto.
apply red_incl with (1 := cs) (p := addEnd a l); auto.
apply addEnd_incl; auto.
apply redInclP with (P := l); auto.
apply redInInclQ with (Q := genOCPf l); auto.
apply H'; auto.
apply incl_tran with (m := a :: l); auto.
apply redInclP with (P := l); auto.
apply redInInclQ with (Q := genOCPf l); auto.
apply H'; auto.
apply incl_tran with (m := a :: l); auto.
Qed.

Theorem OBuch_Stable_f :
 forall P Q : list poly, OBuch P (genOCPf P) Q -> stable P Q.
Proof.
intros P Q H'; try assumption.
apply OBuch_Stable with (Q := genOCPf P); auto.
intros a H'0; try assumption.
apply genOCPf_stable; auto.
Qed.

Theorem OBuch_Inv_f :
 forall P Q : list poly,
 OBuch P (genOCPf P) Q ->
 forall a b : poly, In a Q -> In b Q -> reds a b Q.
Proof.
intros P Q H' a b H'0 H'1; try assumption.
apply OBuch_Inv with (aP := P) (Q := genOCPf P); auto.
intros a0 b0 H'3 H'4.
apply genOCp_redln; auto.
apply ObuchPincl with (Q := genOCPf P); auto.
Qed.

Let FPset (A : list poly) := list poly.
 
Definition Fl : forall x : list poly, FPset x -> FPset x -> Prop.
unfold FPset in |- *; simpl in |- *.
intros H' P1 P2.
exact (Tl P1 P2).
Defined.
 
Theorem wf_Fl : forall x : list poly, well_founded (Fl x).
Proof.
unfold FPset in |- *; simpl in |- *.
intros x; generalize wf_Tl; auto.
Qed.

Let Co :=
  @lexprod (list poly) FPset
    (RO A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os)
    Fl.

Theorem wf_Co : well_founded Co.
Proof.
unfold Co in |- *; apply wf_lexprod.
apply wf_incl.
exact wf_Fl.
Qed.
 
Definition PtoS :
  list poly * list poly -> sigT FPset.
intros H'; case H'.
intros P1 P2.
exact (existT FPset P1 P2).
Defined.
 
Definition RL (x y : list poly * list poly) :
  Prop := Co (PtoS x) (PtoS y).
 
Theorem wf_RL : well_founded RL.
Proof.
apply (wf_inverse_image _ _ Co PtoS); auto.
try exact wf_Co.
Qed.
 
Definition pbuchf :
  forall PQ : list poly * list poly,
  {R : list poly | OBuch (fst PQ) (snd PQ) R}.
intros pq; pattern pq in |- *.
apply
 well_founded_induction_type
  with
    (A := (list poly * list poly)%type)
    (R := RL).
try exact wf_RL.
intros x; elim x.
intros P Q; case Q; simpl in |- *.
intros H'; exists P; auto.
intros a Q2 Rec.
apply LetP with (A := poly) (h := nf a P).
intros a0 H'.
case (zerop_dec A A0 eqA n ltM a0); intros red10.
elim (Rec (P, Q2)); simpl in |- *; [ intros R E | idtac ]; auto.
exists R; auto.
apply OBuch2; auto.
rewrite <- H'; auto.
red in |- *; unfold Co in |- *; unfold PtoS in |- *.
apply
 (right_lex _ _
    (RO A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os)
    Fl); auto.
red in |- *; red in |- *; simpl in |- *; auto.
elim (Rec (addEnd a0 P, genPcPf a0 P Q2)); simpl in |- *;
 [ intros R E0; try exact E0 | idtac ].
exists R; auto.
apply OBuch1; auto.
rewrite <- H'; auto.
rewrite <- H'; auto.
rewrite H'.
red in |- *; unfold Co in |- *; unfold PtoS in |- *.
apply
 (left_lex _ _
    (RO A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os)
    Fl); auto.
apply RO_lem; auto.
rewrite <- H'; auto.
Defined.
 
Definition strip :
  forall P : list poly -> Prop, sig P -> list poly.
intros P H'; case H'.
intros x H'0; try assumption.
Defined.
 
Theorem pbuchf_Stable :
 forall P R : list poly,
 R = strip _ (pbuchf (P, genOCPf P)) -> stable P R.
Proof.
simpl in |- *.
intros P R H'; try assumption.
apply OBuch_Stable_f; auto.
rewrite H'.
case (pbuchf (pair P (genOCPf P))); simpl in |- *; auto.
Qed.

Theorem pbuchf_Inv :
 forall P R : list poly,
 R = strip _ (pbuchf (P, genOCPf P)) ->
 forall a b : poly, In a R -> In b R -> reds a b R.
Proof.
intros P R H' a b H'0 H'1; simpl in |- *.
apply OBuch_Inv_f with (P := P); auto.
rewrite H'; simpl in |- *; auto.
case (pbuchf (P, genOCPf P)); simpl in |- *; auto.
Qed.
 
Definition buch : list poly -> list poly.
intros P; exact (strip _ (pbuchf (P, genOCPf P))).
Defined.
 
Theorem buch_Stable : forall P : list poly, stable P (buch P).
Proof.
intros P; apply pbuchf_Stable; auto.
Qed.
 
Theorem buch_reds :
 forall (P : list poly) (a b : poly),
 In a (buch P) -> In b (buch P) -> reds a b (buch P).
Proof.
intros P a b H' H'0.
apply pbuchf_Inv with (P := P); auto.
Qed.

Notation Spoly_1 := (Spoly_1 _ _ _ _ _ _ _ _ _ cs eqA_dec n ltM ltM_dec).
Notation s2p := (s2p A A0 eqA n ltM).
Notation inPolySet := (inPolySet A A0 eqA n ltM).

Theorem reds_SpolyQ :
 forall (P : list poly) (a b : poly),
 reds a b P -> Spoly_1 P (s2p a) (s2p b).
Proof.
intros P a b H'; elim H'; auto.
intros P0 a0 b0 H'0; cut (red (spolyp b0 a0) P0); auto.
case a0; case b0; unfold red in |- *; simpl in |- *; auto.
intros x H'1 x0 H'2 H'3; inversion H'3.
apply Spoly_10 with (Cp := H'2) (Cq := H'1); auto.
apply red_com; auto.
intros P0 a0 b0 c.
case c; case b0; case a0; simpl in |- *.
intros x; case x; simpl in |- *; auto.
intros c0 x0 c1 x1 c2 H'0 H'1 H'2 H'3 H'4 H'5; elim H'5.
intros a1 l c0 x0; case x0; simpl in |- *.
intros c1 x1 c2 H'0 H'1 H'2 H'3 H'4 H'5; elim H'5.
intros a2 l0 c1 x1; case x1; simpl in |- *.
intros c2 H'0 H'1 H'2 H'3 H'4 H'5; elim H'5.
intros a3 l1 c2 H'0 H'1 H'2 H'3 H'4 H'5.
change (Spoly_1 P0 (pX a1 l) (pX a2 l0)) in |- *.
apply Spoly_11 with (d := a3) (t := l1); auto.
change (inPolySet (s2p (mks A A0 eqA n ltM (pX a3 l1) c2)) P0) 
 in |- *.
apply in_inPolySet; simpl in |- *; auto.
red in |- *; intros H; inversion H.
Qed.

Theorem imp_in :
 forall (P : list poly) (a : list (Term A n)),
 inPolySet a P -> exists b : poly, In b P /\ a = s2p b.
Proof.
intros P a H'; elim H'; auto.
intros a0 p H P0;
 exists
  (exist (fun l0 : list (Term A n) => canonical A0 eqA ltM l0) (pX a0 p) H);
 split; auto.
simpl in |- *; auto.
intros a0 p P0 H'0 H'1; elim H'1; intros b E; elim E; intros H'2 H'3;
 clear E H'1; auto.
exists b; split; auto with datatypes.
Qed.

Notation SpolyQ := (SpolyQ _ _ _ _ _ _ _ _ _ cs eqA_dec _ _ ltM_dec).

Theorem reds_SpolyQ1 :
 forall P : list poly,
 (forall a b : poly, In a P -> In b P -> reds a b P) -> SpolyQ P.
Proof.
intros P H'.
apply SpolyQ0; auto.
intros p q H'0 H'1 H'2 H'3.
elim (imp_in P p); [ intros b E; elim E; intros H'7 H'8; clear E | idtac ];
 auto.
rewrite H'8.
elim (imp_in P q); [ intros b0 E; elim E; intros H'9 H'10; clear E | idtac ];
 auto.
rewrite H'10.
apply reds_SpolyQ; auto.
Qed.

Theorem buch_spolyQ : forall P : list poly, SpolyQ (buch P).
Proof.
intros P.
apply reds_SpolyQ1; auto.
intros; apply buch_reds; auto.
Qed.

Notation Grobner := (Grobner A A0 A1 eqA plusA invA minusA multA divA eqA_dec n ltM ltM_dec).

Theorem buch_Grobner : forall P : list poly, Grobner (buch P).
Proof.
intros P.
apply ConfluentReduce_imp_Grobner; auto.
apply SpolyQ_imp_ConfluentReduce with (1 := os) (cs := cs).
apply buch_spolyQ; auto.
Qed.

End Buch.
