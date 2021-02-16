(* Unit-free MLL following Yalla schemas *)

From Coq Require Import Bool Wf_nat Lia.
From OLlibs Require Import dectype funtheory List_more List_Type Permutation_Type_more.

Import EqNotations.

Set Implicit Arguments.

(** * MLL formulas *)

Section Atoms.

(** A set of atoms for building formulas *)
Context { atom : DecType }.

(** Formulas *)
Inductive formula :=
| var : atom -> formula
| covar : atom -> formula
| tens : formula -> formula -> formula
| parr : formula -> formula -> formula.
Notation "'ν' X" := (var X) (at level 12).
Notation "'κ' X" := (covar X) (at level 12).
Infix "⊗" := tens (at level 40).
Infix "⅋" := parr (at level 40).

(** ** Equality of [formula] in [bool] *)
Fixpoint eqb_form A B :=
match A, B with
| var X, var Y => eqb X Y
| covar X, covar Y => eqb X Y
| tens A1 A2, tens B1 B2 => eqb_form A1 B1 && eqb_form A2 B2
| parr A1 A2, parr B1 B2 => eqb_form A1 B1 && eqb_form A2 B2
| _, _ => false
end.

Lemma eqb_eq_form : forall A B, eqb_form A B = true <-> A = B.
Proof.
induction A; destruct B; (split; intros Heq); inversion Heq; auto.
- now apply eqb_eq in H0; subst.
- now subst; cbn; apply eqb_eq.
- now apply eqb_eq in H0; subst.
- now subst; cbn; apply eqb_eq.
- apply andb_true_iff in H0.
  destruct H0 as [H1 H2].
  now apply IHA1 in H1; apply IHA2 in H2; subst.
- now subst; cbn; apply andb_true_iff; split; [ apply IHA1 | apply IHA2 ].
- apply andb_true_iff in H0 as [H1 H2].
  now apply IHA1 in H1; apply IHA2 in H2; subst.
- now subst; cbn; apply andb_true_iff; split; [ apply IHA1 | apply IHA2 ].
Qed.

Definition formulas_dectype := {|
  car := formula;
  eqb := eqb_form;
  eqb_eq := eqb_eq_form |}.

(** ** Dual of a [formula] *)
Fixpoint dual A :=
match A with
| var x     => covar x
| covar x   => var x
| tens A B  => parr (dual B) (dual A)
| parr A B  => tens (dual B) (dual A)
end.
Notation "A ^" := (dual A) (at level 12, format "A ^").

Lemma bidual A : dual (dual A) = A.
Proof. now induction A; cbn; rewrite ? IHA1, ? IHA2, ? IHA. Qed.

Lemma codual A B : dual A = B <-> A = dual B.
Proof. now split; intro H; rewrite <- (bidual A), <- (bidual B), H, ? bidual. Qed.

Lemma dual_inj : injective dual.
Proof. now intros A B H; rewrite <- (bidual A), <- (bidual B), H. Qed.

(** ** Size of a [formula] as its number of symbols *)
Fixpoint fsize A :=
match A with
| var X    => 1
| covar X  => 1
| tens A B => S (fsize A + fsize B)
| parr A B => S (fsize A + fsize B)
end.

Lemma fsize_pos A : 0 < fsize A.
Proof. induction A; cbn; lia. Qed.

Lemma fsize_dual A : fsize (dual A) = fsize A.
Proof. induction A; cbn; rewrite ? IHA1, ? IHA2; lia. Qed.


(** * MLL Proofs *)
Inductive ll : list formula -> Type :=
| ax_r : forall X, ll (covar X :: var X :: nil)
| ex_r : forall l1 l2, ll l1 -> Permutation_Type l1 l2 -> ll l2
| tens_r : forall A B l1 l2, ll (A :: l1) -> ll (B :: l2) -> ll (tens A B :: l2 ++ l1)
| parr_r : forall A B l, ll (A :: B :: l) -> ll (parr A B :: l)
| cut_r : forall A l1 l2 l3 l4, ll (l1 ++ A :: l2) ->
             ll (l3 ++ dual A :: l4) -> ll (l3 ++ l2 ++ l1 ++ l4).
Notation "⊢ l" := (ll l) (at level 70).

(** ** Size of proofs *)
Fixpoint psize l (pi : ll l) :=
match pi with
| ax_r _ => 1
| ex_r pi0 _ => S (psize pi0)
| tens_r pi1 pi2 => S (psize pi1 + psize pi2)
| parr_r pi0 => S (psize pi0)
| cut_r _ _ _ _ _ pi1 pi2 => S (psize pi1 + psize pi2)
end.

Lemma psize_pos l (pi : ll l) : 0 < psize pi.
Proof. destruct pi; cbn; lia. Qed.

Lemma psize_rew l l' (pi : ll l) (Heq : l = l') : psize (rew Heq in pi) = psize pi.
Proof. now subst. Qed.

Lemma psize_rew_r l l' (pi : ll l) (Heq : l' = l) : psize (rew <- Heq in pi) = psize pi.
Proof. now subst. Qed.

Lemma app_assoc_cons [T:Type] (a:T) (x y z : list T) : a :: x ++ y ++ z = a :: (x ++ y) ++ z.
Proof. now rewrite app_assoc. Qed.

Lemma app_assoc_cons2 [T:Type] (a b:T) (x y z : list T) : a :: x ++ b :: y ++ z = a :: (x ++ b :: y) ++ z.
Proof. now rewrite <- app_assoc, <- app_comm_cons. Qed.

Lemma app_assoc_cons3 [T:Type] (a:T) (x y z t u : list T) : a :: x ++ y ++ z ++ t ++ u =  a :: (x ++ y ++ z ++ t) ++ u.
Proof. now rewrite <- 3 app_assoc. Qed.

Lemma app_assoc2 [T:Type] (x y z t: list T) : x ++ y ++ z ++ t = (x ++ y ++ z) ++ t.
Proof. now rewrite <- 2 app_assoc. Qed.

Lemma app_bidual a x y : x++a::y = x++(dual (dual a))::y.
Proof. now rewrite bidual. Qed.



Lemma psize_rew_fun (l : list formula) l' f (pi : ll (f l)) (Heq : l = l') : psize (rew [fun x => ll (f x)] Heq in pi) = psize pi.
Proof. now subst. Qed.

Lemma psize_rew_fun_r (l : list formula) l' f (pi : ll (f l)) (Heq : l' = l) : psize (rew <- [fun x => ll (f x)] Heq in pi) = psize pi.
Proof. now subst. Qed.



Inductive red : forall l, ll l -> ll l -> Prop :=
| ax_v : forall A l1 l2 (pi : ll (l1 ++ var A::nil ++ l2)),
    red (cut_r _ l1 l2 nil _ pi (ax_r A))
      (ex_r pi (Permutation_Type_sym (Permutation_Type_app_rot l2 l1 (var A::nil))))
| ax_cv : forall A l1 l2 (pi : ll (l1 ++ covar A::nil ++ l2)),
    red (cut_r _ l1 l2 (covar A :: nil) nil pi (ax_r A))
      (rew <- (app_assoc2 _ _ _ _) in (rew (app_nil_end _) in (ex_r pi (Permutation_Type_app_rot l1 (covar A::nil) l2))))
| parr_d : forall A B C l1 l2 l3 l4 (pi1 : ll (l1 ++ C::l2)) (pi2 : ll ((A::B::l3) ++ dual C :: l4)),
    red (cut_r _ _ _ (parr A B :: l3) _ pi1 (parr_r pi2)) (parr_r (cut_r _ _ _ _ _ pi1 pi2))
| tens_parr : forall A B l1 l2 l3 (pi1 : ll (A::l1)) (pi2 : ll (B::l2)) (pi3 : ll (dual B:: dual A::l3)),
    red (rew <- (app_assoc _ _ _) in (cut_r _ nil _ nil _ (tens_r pi1 pi2) (parr_r pi3)))
      (cut_r _ nil _ _ _ pi1 (cut_r _ nil _ nil _ pi2 pi3))
| tens_dg : forall A B C l1 l2 l3 l4 l5 (pi1 : ll (l1 ++ C :: l2)) (pi2 : ll (A::l3)) (pi3 : ll (B::l4 ++ dual C::l5)),
    red (rew <- (app_comm_cons _ _ _) in (cut_r C _ _ (tens A B :: l4) (l5++l3) pi1 (rew <- (app_assoc_cons2 _ _ _ _ _) in (tens_r pi2 pi3))))
      (rew <- (app_assoc_cons3 _ _ _ _ _ _) in (tens_r pi2 (cut_r C l1 l2 (B :: l4) l5 pi1 pi3) : ll (tens A B :: (l4 ++ l2 ++ l1 ++ l5) ++ l3)))
| tens_dd : forall A B C l1 l2 l3 l4 l5 (pi1 : ll (l1 ++ C :: l2)) (pi2 : ll (A::l3 ++ dual C::l4)) (pi3 : ll (B::l5)),
    red (rew <- (app_assoc_cons _ _ _ _) in (rew <- (app_comm_cons _ _ _) in
      (cut_r C _ _ (tens A B :: l5 ++ l3) l4 pi1 (rew (app_assoc_cons _ _ _ _) in (tens_r pi2 pi3)))))
        (tens_r (cut_r C l1 l2 (A::l3) l4 pi1 pi2) pi3)
| ex_d : forall A l1 l2 l3 l4 l5 l6 (pi1 : ll (l1 ++ A::l2)) (pi2 : ll (l3 ++ dual A :: l4)) (P : Permutation_Type (l3 ++ dual A::l4) (l5 ++ dual A :: l6)),
    red (cut_r A _ _ _ _ pi1 (ex_r pi2 P))
      (ex_r (cut_r _ _ _ _ _ pi1 pi2) (Permutation_Type_app_middle l2 _ _ _ _ (Permutation_Type_app_middle l1 _ _ _ _ (Permutation_Type_app_inv _ _ _ _ _ P))))
| parr_rec : forall A B l (pi1 : ll (A :: B :: l)) (pi2 : ll (A :: B :: l)), red pi1 pi2 -> red (parr_r pi1) (parr_r pi2)
| tens_rec_g : forall A B l1 l2 (pi1 : ll (A :: l1)) (pi2 : ll (A :: l1)) (pi3 : ll (B :: l2)), red pi1 pi2 -> red (tens_r pi1 pi3) (tens_r pi2 pi3)
| tens_rec_d : forall A B l1 l2 (pi1 : ll (A :: l1)) (pi2 : ll (B :: l2)) (pi3 : ll (B :: l2)), red pi2 pi3 -> red (tens_r pi1 pi2) (tens_r pi1 pi3)
| ex_rec : forall l1 l2 (P : Permutation_Type l1 l2) (pi1 : ll l1) (pi2 : ll l1), red pi1 pi2 -> red (ex_r pi1 P) (ex_r pi2 P)
| cut_sym : forall A l1 l2 l3 l4 (pi1 : ll (l1++A::l2)) (pi2 : ll (l3++dual A::l4)) (pi3 : ll (l1++l4++l3++l2)),
    red (cut_r _ _ _ _ _ pi1 pi2) (rew <- (app_assoc _ _ _) in
      (ex_r pi3 (Permutation_Type_trans (Permutation_Type_app_rot _ _ _) (Permutation_Type_app_rot _ _ _))))
    -> red (cut_r _ _ _ l1 l2 pi2 (rew (app_bidual _ _ _) in pi1)) pi3
(*
| tens_dg2 : forall A B C l1 l2 l3 l4 l5 (pi1 : ll (l1 ++ C :: l2)) (pi2 : ll (A::l3)) (pi3 : ll (B::l4 ++ dual C::l5)),
    red (rew <- (app_comm_cons _ _ _) in (cut_r C _ _ (tens A B :: l4) (l5++l3) pi1 (rew <- [fun x => ll (_ :: _ ++ x)] (app_comm_cons _ _ _) in
        (rew <- [fun x => ll (_ :: x)] (app_assoc _ _ _) in (tens_r pi2 pi3)))))
      (rew <- [fun x => ll (_ :: _ ++ _ ++ x)] (app_assoc _ _ _) in (rew <- [fun x => ll (_ :: _ ++ x)] (app_assoc _ _ _) in 
        (rew <- [fun x => ll (_ :: x)] (app_assoc _ _ _) in (tens_r pi2 (cut_r C l1 l2 (B :: l4) l5 pi1 pi3) : ll (tens A B :: (l4 ++ l2 ++ l1 ++ l5) ++ l3)))))
| cut_sym2 : forall A l1 l2 l3 l4 (pi1 : ll (l1++A::l2)) (pi2 : ll (l3++dual A::l4)) (pi3 : ll (l1++l4++l3++l2)),
    red (cut_r _ _ _ _ _ pi1 pi2) (rew <- (app_assoc _ _ _) in
      (ex_r pi3 (Permutation_Type_trans (Permutation_Type_app_rot _ _ _) (Permutation_Type_app_rot _ _ _))))
    -> red (cut_r _ _ _ l1 l2 pi2 (rew <- [fun x => ll (_ ++ x :: _)] (bidual _) in pi1)) pi3
*)
.


Lemma red_size : forall l (pi1 : ll l) (pi2 : ll l), red pi1 pi2 -> psize pi2 <= psize pi1.
Proof.
  intros l pi1 pi2 Hr. Check red_ind.
  induction Hr as [| | | | | | | | | | | A l1 l2 l3 l4 pi1 pi2 pi3 Hr IHr]; try (cbn; unfold app; lia).
  - rewrite psize_rew_r, psize_rew. simpl. lia.
  - rewrite psize_rew_r. simpl. lia.
  - rewrite 2 psize_rew_r. simpl. rewrite psize_rew_r. simpl. lia.
  - rewrite 2 psize_rew_r. simpl. rewrite psize_rew. simpl. lia.
  - simpl. rewrite psize_rew. rewrite psize_rew_r in IHr. simpl in IHr. lia.
Qed.

Lemma red_size2 : forall l (pi1 : ll l) (pi2 : ll l), red pi1 pi2 -> psize pi2 < psize pi1.
Proof.
  intros l pi1 pi2 Hr.
  induction Hr as [| | | | | | | | | | | A l1 l2 l3 l4 pi1 pi2 pi3 Hr IHr]; try (cbn; unfold app; lia).
  - rewrite psize_rew_r, psize_rew. simpl. lia.
  - simpl. admit. (*parr_d*)
  - rewrite psize_rew_r. simpl. lia.
  - rewrite 2 psize_rew_r. simpl. rewrite psize_rew_r. simpl. admit. (*tens_dg*)
  - rewrite 2 psize_rew_r. simpl. rewrite psize_rew. simpl. admit. (*tens_dd*)
  - simpl. admit. (* ex_d *)
  - simpl. rewrite psize_rew. rewrite psize_rew_r in IHr. simpl in IHr. lia.
Abort.

Fixpoint has_cut l (pi : ll l) :=
match pi with
| ax_r _ => False
| ex_r pi0 _ => has_cut pi0
| tens_r pi1 pi2 => (has_cut pi1) \/ (has_cut pi2)
| parr_r pi0 => has_cut pi0
| cut_r _ _ _ _ _ _ _ => True
end.

Lemma has_cut_rew l l' (pi : ll l) (Heq : l = l') : has_cut (rew Heq in pi) <-> has_cut pi.
Proof. now subst. Qed.

Lemma has_cut_rew_r l l' (pi : ll l) (Heq : l' = l) : has_cut (rew <- Heq in pi) <-> has_cut pi.
Proof. now subst. Qed.


Lemma red_term : forall l (pi1 : ll l), has_cut pi1 <-> exists (pi2 : ll l), red pi1 pi2.
Proof.
  intros l pi1. split.
  - induction pi1 ; intro Hcut; simpl in Hcut.
    + destruct Hcut.
    + apply IHpi1 in Hcut. destruct Hcut as [pi2 Hp]. exists (ex_r pi2 p). apply ex_rec, Hp.
    + destruct Hcut as [Hc1 | Hc2].
      * apply IHpi1_1 in Hc1. destruct Hc1 as [pi2 Hp]. exists (tens_r pi2 pi1_2). apply tens_rec_g, Hp.
      * apply IHpi1_2 in Hc2. destruct Hc2 as [pi2 Hp]. exists (tens_r pi1_1 pi2). apply tens_rec_d, Hp.
    + apply IHpi1 in Hcut. destruct Hcut as [pi2 Hp]. exists (parr_r pi2). apply parr_rec, Hp.
    + admit.
  - intros [pi2 Hp].
    induction Hp; simpl; auto.
    + rewrite has_cut_rew_r. now simpl.
    + rewrite has_cut_rew_r. now simpl.
    + rewrite 2 has_cut_rew_r. now simpl.
Admitted.

Lemma cons_eq [T:Type] (a b:T) (x y : list T) : a :: x = b :: y -> a = b /\ x = y.
Proof. split; injection H; auto. Qed.



Lemma dichot [T:Type] (a b c:T) (x y : list T) : a :: b :: nil = x ++ c :: y -> (nil = x /\ a = c /\ b :: nil = y) \/ (a :: nil = x /\ b = c /\ nil = y).
Proof.
  intro H.
  destruct x; [left|right].
  - list_simpl in H.
    inversion H.
    auto.
  - inversion H as [[H1 H2]].
    destruct x.
    + list_simpl in H2.
      inversion H2.
      auto.
    + inversion H2 as [[H3 H4]].
      destruct x; inversion H4.
Qed.


(* sous-preuve du admit ci-dessus *)
Goal forall A l1 l2 l3 l4 (pi1_1 : ll (l1 ++ A :: l2)) (pi1_2 : ll (l3 ++ dual A :: l4)),
  exists (pi2 : ll (l3 ++ l2 ++ l1 ++ l4)), red (cut_r A l1 l2 l3 l4 pi1_1 pi1_2) pi2.
Proof.
  intros A l1 l2 l3 l4 pi1_1 pi1_2.
  assert (exists l, l = l3 ++ dual A :: l4) as [l Heql] by (eexists; reflexivity).
  remember (rew <- Heql in pi1_2) as pi eqn:Heqpi.
  rewrite <- (rew_opp_r _ Heql pi1_2), <- Heqpi; clear Heqpi.
  destruct pi.
  - assert (nil = l3 /\ covar X = dual A /\ var X :: nil = l4  \/  covar X :: nil = l3 /\ var X = dual A /\ nil = l4) as [[H1 [H2 H3]] | [H1 [H2 H3]]] by (now apply dichot).
    + subst.
      revert Heql pi1_1.
      assert (var X = A) as H2' by (rewrite <- bidual, <- H2; auto).
      rewrite <- H2'.
      intros Heql pi1_1.
      cbn in Heql.
      assert (HH := UIP_refl (list_dectype formulas_dectype) Heql).
      rewrite HH.
      cbn.
      exists (ex_r pi1_1 (Permutation_Type_sym (Permutation_Type_app_rot l2 l1 (var X::nil)))).
      apply ax_v.
    + subst.
      revert Heql pi1_1.
      assert (covar X = A) as H2' by (rewrite <- bidual, <- H2; auto).
      rewrite <- H2'.
      intros Heql pi1_1.
      cbn in Heql.
      assert (HH := UIP_refl (list_dectype formulas_dectype) Heql).
      rewrite HH.
      cbn.
      exists (rew <- (app_assoc2 _ _ _ _) in (rew (app_nil_end _) in (ex_r pi1_1 (Permutation_Type_app_rot l1 (covar X::nil) l2)))).
      apply ax_cv.
  - subst.
    cbn.
    assert ({'(l5, l6) | l0 = l5 ++ dual A :: l6}) as [(l5, l6) ->] by (apply (Permutation_Type_vs_elt_inv _ _ _ p)).
    exists (ex_r (cut_r _ _ _ _ _ pi1_1 pi) (Permutation_Type_app_middle l2 _ _ _ _ (Permutation_Type_app_middle l1 _ _ _ _ (Permutation_Type_app_inv _ _ _ _ _ p)))).
    apply ex_d.
  - assert (nil = l3 /\ tens A0 B = dual A /\ l5++l0 = l4 \/ (exists l6 l7, tens A0 B :: l6 = l3 /\ l5 = l6 ++ dual A :: l7 /\ l7++l0 = l4) \/
      (exists l6, tens A0 B :: l5 ++ l6 = l3 /\ l0 = l6 ++ dual A :: l4)) as [[H1 [H2 H3]] | [[l6 [l7 [H1 [H2 H3]]]] | [l6 [H1 H2]]]].
    + assert (l3 ++ A^ :: l4 = (A0 ⊗ B :: nil) ++ l5 ++ l0) as Heql2 by (rewrite <- Heql; apply cons_is_app).
      apply trichot_elt_app in Heql2.
      destruct Heql2 as [[l2' [H1 H2]] | [[l2' [l2'' [H1 [H2 H3]]]] | [l5' [H1 H2]]]].
      * left. apply elt_eq_unit in H1 as [H1 [H3 H4]]. rewrite H4,app_nil_l in H2. auto.
      * right. left. exists l2', l2''. rewrite <- cons_is_app in H1. auto.
      * right. right. exists l5'. rewrite <- cons_is_app in H1. auto.
    + subst.
      revert Heql pi1_1 pi1_2 pi1 pi2.
      assert (parr (dual B) (dual A0) = A) as H2' by (rewrite <- bidual, <- H2; auto).
      rewrite <- H2'.
      simpl dual.
      rewrite (bidual A0). (*
      intros Heql pi1_1 pi1 pi2 pi1_2.
      cbn in Heql.
      assert (A0 ⊗ B :: l5 ++ l0 = (A0^)^ ⊗ (B^)^ :: l5 ++ l0) as H2'' by (now rewrite 2 bidual). *)
      
  
  
  

Abort.



(*

(** * Cut Elimination *)

Ltac destruct_eqrefl H :=
list_simpl in H;
match goal with
| H : ?x = ?x |- _ => assert (H = eq_refl) as ->
                        by apply (Eqdep_dec.UIP_dec (@eq_dt_dec (list_dectype formulas_dectype)));
                      cbn
end.

(** Symmetric induction principle *)
Lemma sym_induction_ll (P : forall [A B l1 l2 l3 l4], ll (l1 ++ A :: l2) -> ll (l3 ++ B :: l4)
                          -> Type) :
  (forall A B l1 l2 l3 l4 (pi1 : ll (l1 ++ A :: l2)) (pi2 : ll (l3 ++ B :: l4)),
     P pi2 pi1 -> P pi1 pi2) ->
  (forall X B l3 l4 (pi2 : ll (l3 ++ B :: l4)),
     P (ax_r X : ll (nil ++ covar X :: var X :: nil)) pi2) ->
  (forall X B l3 l4 (pi2 : ll (l3 ++ B :: l4)),
     P (ax_r X : ll ((covar X :: nil) ++ var X :: nil)) pi2) ->
  (forall A B l1 l2 l3 l4 l' (pi1 : ll l') (pi2 : ll (l3 ++ B :: l4))
     (HP : Permutation_Type l' (l1 ++ A :: l2)),
     P (rew (rew (surjective_pairing (proj1_sig (Permutation_Type_vs_elt_inv _ _ _ HP)))
              in proj2_sig (Permutation_Type_vs_elt_inv _ _ _ HP)) in pi1) pi2 ->
     P (ex_r pi1 HP) pi2) ->
  (forall A B C D l0 l1 l2 l3 l4 (pi0 : ll (C :: l0))
     (pi1 : ll (D :: l1 ++ A :: l2)) (pi2 : ll (l3 ++ B :: l4)),
     P (pi1 : ll ((D :: l1) ++ A :: l2)) pi2 ->
     P (rew <- (app_assoc (tens C D :: l1) (A :: l2) _) in tens_r pi0 pi1) pi2) ->
  (forall A B C D l0 l1 l2 l3 l4 (pi0 : ll (D :: l0))
     (pi1 : ll (C :: l1 ++ A :: l2)) (pi2 : ll (l3 ++ B :: l4)),
     P (pi1 : ll ((C :: l1) ++ A :: l2)) pi2 ->
     P (rew (app_assoc (tens C D :: l0) _ (A :: l2)) in tens_r pi1 pi0 ) pi2) ->
  (forall A B C D l1 l2 l3 l4 (pi1 : ll (C :: D :: l1 ++ A :: l2)) (pi2 : ll (l3 ++ B :: l4)),
     P (pi1 : ll ((C :: D :: l1) ++ A :: l2)) pi2 ->
     P (parr_r pi1 : ll ((parr C D :: l1) ++ A :: l2)) pi2) ->
  (forall C D C' D' l2' l2'' (pi1' : ll (C :: l2')) (pi1'' : ll (D :: l2'')),
     (forall l3 l4 (pi2 : ll (l3 ++ C' :: l4)), P (pi1' : ll (nil ++ _)) pi2) ->
     (forall l3 l4 (pi2 : ll (l3 ++ D' :: l4)), P (pi1'' : ll (nil ++ _)) pi2) ->
     forall l4' l4'' (pi2' : ll (C' :: l4')) (pi2'' : ll (D' :: l4'')),
       P (tens_r pi1' pi1'' : ll (nil ++ _)) (tens_r pi2' pi2'' : ll (nil ++ _))) ->
  (forall C D C' D' l2 (pi1 : ll (C :: D :: l2)),
     (forall l3 l4 (pi2 : ll (l3 ++ C' :: l4)), P (pi1 : ll (nil ++ _)) pi2) ->
      forall l4 (pi2 : ll (C' :: D' :: l4)),
       P (parr_r pi1 : ll (nil ++ _)) (parr_r pi2 : ll (nil ++ _))) ->
  (forall C D C' D' l1' l1'' (pi1' : ll (C :: l1')) (pi1'' : ll (D :: l1'')),
     (forall l3 l4 (pi2 : ll (l3 ++ C' :: l4)), P (pi1' : ll (nil ++ _)) pi2) ->
     (forall l3 l4 (pi2 : ll (l3 ++ D' :: l4)), P (pi1'' : ll (nil ++ _)) pi2) ->
     forall l4 (pi2 : ll (D' :: C' :: l4)),
       P (tens_r pi1' pi1'' : ll (nil ++ _)) (parr_r pi2 : ll (nil ++ _))) ->
  forall A B l1 l2 l3 l4 (pi1 : ll (l1 ++ A :: l2)) (pi2 : ll (l3 ++ B :: l4)), P pi1 pi2.
Proof.
intros Hsym Hax1 Hax2 Hex Htens1 Htens2 Hparr Htt Hpp Htp.
enough (forall c s A B s1 s2 (pi1 : ll s1) (pi2 : ll s2),
          s = psize pi1 + psize pi2 -> fsize A <= c -> fsize B <= c ->
          forall l1 l2 l3 l4 (Heq1 : s1 = l1 ++ A :: l2) (Heq2 : s2 = l3 ++ B :: l4),
          P A B l1 l2 l3 l4 (rew Heq1 in pi1) (rew Heq2 in pi2)) as IH
  by (now intros A B l1 l2 l3 l4 pi1 pi2;
          refine (IH (max (fsize A) (fsize B)) _ _ _ _ _ pi1 pi2 _ _ _ _ _ _ _ eq_refl eq_refl);
          try lia).
induction c as [c IHf0] using lt_wf_rect.
assert (forall A B, fsize A < c -> fsize B < c ->
          forall l1 l2 l3 l4 pi1 pi2, P A B l1 l2 l3 l4 pi1 pi2) as IHf
  by (now intros A B HA HB l1 l2 l3 l4 pi1 pi2;
          refine (IHf0 (max (fsize A) (fsize B)) _ _ A _ _ _ pi1 pi2 _ _ _ _ _ _ _ eq_refl eq_refl);
          try lia); clear IHf0.
induction s as [s IHp0] using lt_wf_rect.
assert (forall A B l1 l2 l3 l4 pi1 pi2, psize pi1 + psize pi2 < s -> fsize A <= c -> fsize B <= c ->
          P A B l1 l2 l3 l4 pi1 pi2) as IHp
  by (now intros A B l1 l2 l3 l4 pi1 pi2 Hp HA HB;
          refine (IHp0 _ Hp _ _ _ _ pi1 pi2 _ _ _ _ _ _ _ eq_refl eq_refl)); clear IHp0.
intros A B s1 s2 pi1 pi2 Heqs HA HB l1 l2 l3 l4 Heq1 Heq2; rewrite_all Heqs; clear s Heqs.
destruct pi1.
- destruct l1; inversion Heq1; subst; cbn in Heq1.
  + destruct_eqrefl Heq1; apply Hax1.
  + destruct l1; inversion Heq1; subst.
    * destruct_eqrefl Heq1; apply Hax2.
    * exfalso; destruct l1; inversion Heq1.
- subst; cbn; apply Hex, IHp; cbn; rewrite ? psize_rew; lia.
- destruct l1; inversion Heq1.
  + destruct pi2; subst; cbn in HA; destruct_eqrefl Heq1.
    * repeat (destruct l3; inversion Heq2); subst; destruct_eqrefl Heq2; apply Hsym;
        [ apply Hax1 | apply Hax2 ].
    * apply Hsym, Hex, IHp; cbn; rewrite ? psize_rew; lia.
    * destruct l3; inversion Heq2; subst; cbn in HB.
      -- destruct_eqrefl Heq2.
         apply Htt; intros; apply IHf; lia.
      -- apply Hsym.
         dichot_elt_app_inf_exec H1; subst.
         ++ replace (rew [ll] Heq2 in tens_r pi2_1 pi2_2)
               with (rew <- (app_assoc (tens A1 B1 :: l3) _ _) in tens_r pi2_1 pi2_2).
            ** apply Htens1, IHp; cbn; try lia.
            ** rewrite <- (rew_opp_l ll (app_assoc (tens A1 B1 :: l3) (B :: l) l1)).
               f_equal; rewrite rew_compose.
               now assert (eq_trans Heq2 (app_assoc (tens A1 B1 :: l3) (B :: l) l1) = eq_refl)
                     as -> by apply (Eqdep_dec.UIP_dec (@eq_dt_dec (list_dectype formulas_dectype)));
                   cbn.
         ++ replace (rew [ll] Heq2 in tens_r pi2_1 pi2_2)
               with (rew (app_assoc (tens A1 B1 :: l6) _ _) in tens_r pi2_1 pi2_2).
            ** apply Htens2, IHp; cbn; lia.
            ** rewrite <- (rew_opp_r ll (app_assoc (tens A1 B1 :: l6) l2 (B :: l4))).
               f_equal; unfold eq_rect_r; rewrite rew_compose.
               now assert (eq_trans Heq2 (eq_sym (app_assoc (tens A1 B1 :: l6) l2 (B :: l4)))
                         = eq_refl)
                     as -> by apply (Eqdep_dec.UIP_dec (@eq_dt_dec (list_dectype formulas_dectype)));
                   cbn.
    * destruct l3; inversion Heq2; subst; destruct_eqrefl Heq2; cbn in HB.
      -- apply Htp; intros; apply IHf; lia.
      -- apply Hsym, Hparr, IHp; cbn; lia.
  + subst; cbn.
    dichot_elt_app_inf_exec H1; subst.
    * change ((tens A0 B0 :: l1) ++ A :: l ++ l0) with (tens A0 B0 :: l1 ++ A :: l ++ l0) in Heq1.
      replace (rew [ll] Heq1 in tens_r pi1_1 pi1_2)
         with (rew <- (app_assoc (tens A0 B0 :: l1) _ _) in tens_r pi1_1 pi1_2).
      -- apply Htens1, IHp; cbn; lia.
      -- rewrite <- (rew_opp_l ll (app_assoc (tens A0 B0 :: l1) (A :: l) l0)).
           f_equal; rewrite rew_compose.
           now assert (eq_trans Heq1 (app_assoc (tens A0 B0 :: l1) (A :: l) l0) = eq_refl)
                 as -> by apply (Eqdep_dec.UIP_dec (@eq_dt_dec (list_dectype formulas_dectype)));
               cbn.
    * change ((tens A0 B0 :: l5 ++ l6) ++ A :: l2)
        with (tens A0 B0 :: (l5 ++ l6) ++ A :: l2) in Heq1.
      replace (rew [ll] Heq1 in tens_r pi1_1 pi1_2)
         with (rew (app_assoc (tens A0 B0 :: l5) _ _) in tens_r pi1_1 pi1_2).
      -- apply Htens2, IHp; cbn; lia.
      -- rewrite <- (rew_opp_r ll (app_assoc (tens A0 B0 :: l5) l6 (A :: l2))).
         f_equal; unfold eq_rect_r; rewrite rew_compose.
         now assert (eq_trans Heq1 (eq_sym (app_assoc (tens A0 B0 :: l5) l6 (A :: l2))) = eq_refl)
               as -> by apply (Eqdep_dec.UIP_dec (@eq_dt_dec (list_dectype formulas_dectype)));
             cbn.
- destruct l1; inversion Heq1.
  + destruct pi2; subst; cbn in HA; destruct_eqrefl Heq1.
    * repeat (destruct l3; inversion Heq2); subst; destruct_eqrefl Heq2; apply Hsym;
        [ apply Hax1 | apply Hax2 ].
    * apply Hsym, Hex, IHp; cbn; rewrite ? psize_rew; lia.
    * destruct l3; inversion Heq2; subst; cbn in HB.
      -- destruct_eqrefl Heq2.
         apply Hsym, Htp; intros; apply IHf; lia.
      -- apply Hsym; cbn.
         dichot_elt_app_inf_exec H1; subst.
         ++ change ((tens A1 B1 :: l3) ++ B :: l ++ l1)
              with (tens A1 B1 :: l3 ++ B :: l ++ l1) in Heq2.
            replace (rew [ll] Heq2 in tens_r pi2_1 pi2_2)
               with (rew <- (app_assoc (tens A1 B1 :: l3) _ _) in tens_r pi2_1 pi2_2).
            ** apply Htens1, IHp; cbn; lia.
            ** rewrite <- (rew_opp_l ll (app_assoc (tens A1 B1 :: l3) (B :: l) l1)).
               f_equal; rewrite rew_compose.
               now assert (eq_trans Heq2 (app_assoc (tens A1 B1 :: l3) (B :: l) l1) = eq_refl)
                     as -> by apply (Eqdep_dec.UIP_dec (@eq_dt_dec (list_dectype formulas_dectype)));
                   cbn.
         ++ change ((tens A1 B1 :: l0 ++ l5) ++ B :: l4)
              with (tens A1 B1 :: (l0 ++ l5) ++ B :: l4) in Heq2.
            replace (rew [ll] Heq2 in tens_r pi2_1 pi2_2)
               with (rew (app_assoc (tens A1 B1 :: l0) _ _) in tens_r pi2_1 pi2_2).
            ** apply Htens2, IHp; cbn; lia.
            ** rewrite <- (rew_opp_r ll (app_assoc (tens A1 B1 :: l0) l5 (B :: l4))).
               f_equal; unfold eq_rect_r; rewrite rew_compose.
               now assert (eq_trans Heq2 (eq_sym (app_assoc (tens A1 B1 :: l0) l5 (B :: l4)))
                         = eq_refl)
                     as -> by apply (Eqdep_dec.UIP_dec (@eq_dt_dec (list_dectype formulas_dectype)));
                   cbn.
    * destruct l3; inversion Heq2; subst; cbn in HB; destruct_eqrefl Heq2.
      -- apply Hpp; intros; apply IHf; lia.
      -- apply Hsym, Hparr, IHp; cbn; lia.
  + subst; cbn; destruct_eqrefl Heq1.
    apply Hparr, IHp; cbn; lia.
Qed.

Theorem cut A l1 l2 l3 l4 :
  ll (l1 ++ A :: l2) -> ll (l3 ++ dual A :: l4) -> ll (l3 ++ l2 ++ l1 ++ l4).
Proof.
intros pi1 pi2; assert (Heq := eq_refl (dual A)); revert pi1 pi2 Heq.
apply (sym_induction_ll (fun A B l1 l2 l3 l4 pi1 pi2 => B = dual A -> ll (l3 ++ l2 ++ l1 ++ l4)));
  clear A l1 l2 l3 l4; cbn; try now intuition subst.
- intros A B l1 l2 l3 l4 pi1 pi2 pi ->.
  apply (ex_r (pi (eq_sym (bidual A)))).
  rewrite (app_assoc l1), (app_assoc l3); apply Permutation_Type_app_comm.
- intros A B l1 l2 l3 l4 l' pi1 pi2 HP.
  destruct (Permutation_Type_vs_elt_inv A l1 l2 HP) as [(l1', l2') ->]; cbn in pi1, HP; cbn.
  intros pi0' pi0; apply pi0' in pi0; clear - HP pi0.
  apply (ex_r pi0).
  apply Permutation_Type_app_head; rewrite ? app_assoc; apply Permutation_Type_app_tail.
  transitivity (l1' ++ l2'); [ apply Permutation_Type_app_comm | ].
  transitivity (l1 ++ l2); [ | apply Permutation_Type_app_comm ].
  apply (Permutation_Type_app_inv _ _ _ _ _ HP).
- intros A B C D l0 l1 l2 l3 l4 pi1 pi2 pi3 pi4 ->.
  change (ll (l3 ++ (l2 ++ l0) ++ tens C D :: l1 ++ l4)).
  apply ex_r with (tens C D :: ((l1 ++ l4) ++ l3 ++ l2) ++ l0); [ apply tens_r; trivial | ].
  + apply (ex_r (pi4 eq_refl)).
    rewrite app_assoc; apply Permutation_Type_app_comm.
  + list_simpl; rewrite app_comm_cons, app_assoc, ? (app_assoc l3), (app_assoc (l3 ++ l2)).
    apply Permutation_Type_app_comm.
- intros A B C D l0 l1 l2 l3 l4 pi1 pi2 pi3 pi4' pi4; apply pi4' in pi4; clear pi4'.
  apply ex_r with (tens C D :: l0 ++ (l1 ++ l4) ++ l3 ++ l2); [ apply tens_r; trivial | ].
  + apply (ex_r pi4).
    rewrite app_assoc; apply Permutation_Type_app_comm.
  + list_simpl; rewrite app_comm_cons, ? (app_assoc l3), ? app_assoc, <- app_assoc.
    apply Permutation_Type_app_comm.
- intros A B C D l1 l2 l3 l4 pi1 pi2 pi3' pi3; apply pi3' in pi3; clear pi3'.
  apply ex_r with (parr C D :: (l1 ++ l4) ++ l3 ++ l2); [ apply parr_r, (ex_r pi3) | ].
  + rewrite app_assoc; apply Permutation_Type_app_comm.
  + list_simpl; rewrite app_comm_cons, ? app_assoc, <- app_assoc.
    apply Permutation_Type_app_comm.
- intros C D C' D' l1 l2 pi1 pi2 IHC IHD l0 pi0 Heq; injection Heq as -> ->.
  rewrite <- app_assoc; apply IHC; auto.
  now rewrite <- app_nil_l; apply IHD.
Qed.

*)

End Atoms.
