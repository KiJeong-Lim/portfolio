Require Export Bool.
Require Export PeanoNat.
Require Export Peano_dec.
Require Export List.
Require Export Lia.

Module Helper.

  Import ListNotations.

  Section NaturalNumber.

    Lemma div_mod_property :
      forall a : nat,
      forall b : nat,
      forall q : nat,
      forall r : nat,
      a = b * q + r ->
      r < b ->
      a / b = q /\ a mod b = r.
    Proof.
      assert (forall x : nat, forall y : nat, x > y <-> (exists z : nat, x = S (y + z))).
        intros x y.
        constructor.
        intro.
        induction H.
        exists 0.
        lia.
        destruct IHle as [z H0].
        exists (S z).
        lia.
        intro.
        destruct H as [z H].
        lia.
      intros a b q r H1 H2.
      assert (a = b * (a / b) + (a mod b)).
        apply (Nat.div_mod a b).
        lia.
      assert (0 <= a mod b < b).
        apply (Nat.mod_bound_pos a b).
        lia.
        lia.
      assert (~ q > a / b).
        intro.
        assert (exists z : nat, q = S (a / b + z)).
          apply (H q (a / b)).
          lia.
        destruct H5 as [z H5].
        assert (b + r < a mod b).
          assert (b * q + r >= b * S (a / b) + r).
            lia.
          lia.
        lia.
      assert (~ q < a / b).
        intro.
        assert (exists z : nat, a / b = S (q + z)).
          apply (H (a / b) q).
          lia.
        destruct H6 as [z H6].
        assert (a mod b + r < b).
          assert (b * q + a mod b >= b * S (a / b) + a mod b).
            lia.
          lia.
        lia.
      assert (q = a / b).
        lia.
      assert (r = a mod b).
        lia.
      lia.
    Qed.

    Lemma second_principle_of_finite_induction :
      forall phi : nat -> Prop,
      let phi' : nat -> Prop := fun k : nat => (forall i : nat, i < k -> phi i) in
      (forall k : nat, phi' k -> phi k) ->
      (forall n : nat, phi n).
    Proof.
      intros phi.
      intros phi'.
      intro.
      cut (
        (forall n : nat, phi n /\ phi' n)
      ).
        intro.
        intros n.
        destruct (H0 n).
        apply H1.
      intros n.
      induction n.
      - assert (phi' 0).
          intros i.
          lia.
        constructor.
        apply H.
        apply H0.
        apply H0.
      - assert (phi' (S n)).
          intros i.
          intro.
          inversion H0.
          destruct IHn.
          apply H1.
          subst.
          destruct IHn.
          apply (H3 i).
          lia.
        constructor.
        apply H.
        apply H0.
        apply H0.
    Qed.

    Fixpoint first_nat (p : nat -> bool) (n : nat) : nat :=
      match n with
      | 0 => 0
      | S n' => if p (first_nat p n') then first_nat p n' else n
      end
    .

    Theorem well_ordering_principle : 
      forall p : nat -> bool,
      forall n : nat,
      p n = true ->
      let m := first_nat p n in
      p m = true /\ (forall i : nat, p i = true -> i >= m).
    Proof.
      intros p.
      assert (forall x : nat, p x = true -> p (first_nat p x) = true).
        intros x.
        induction x.
        tauto.
        simpl.
        cut (let b := p (first_nat p x) in p (S x) = true -> p (if b then first_nat p x else S x) = true).
          simpl.
          tauto.
        intros.
        assert (b = true \/ b = false).
          destruct b.
            tauto.
            tauto.
        destruct H0.
        rewrite H0.
        unfold b in H0.
        apply H0.
        rewrite H0.
        apply H.
      assert (forall x : nat, first_nat p x <= x).
        intros x.
        induction x.
          simpl.
          lia.
          simpl.
          cut (let b := p (first_nat p x) in (if b then first_nat p x else S x) <= S x).
            simpl.
            tauto.
          intros.
          assert (b = true \/ b = false).
            destruct b.
              tauto.
              tauto.
          destruct H0.
            rewrite H0.
            lia.
            rewrite H0.
            lia.
      assert (forall x : nat, p (first_nat p x) = true -> (forall y : nat, x < y -> first_nat p x = first_nat p y)).
        intros x.
        intro.
        intros y.
        intro.
        induction H2.
          simpl.
          rewrite H1.
          tauto.
          simpl.
          rewrite <- IHle.
          rewrite H1.
          tauto.
      assert (forall x : nat, forall y : nat, p y = true -> first_nat p x <= y).
        intros x.
        intros y.
        intro.
        assert (x <= y \/ x > y).
          lia.
        destruct H3.
        assert (first_nat p x <= x <= y).
          constructor.
          apply (H0 x).
          apply H3.
          lia.
        assert (p (first_nat p y) = true).
          apply (H y).
          assert (first_nat p x <= x).
            apply (H0 x).
            apply H2.
        assert (first_nat p y = first_nat p x).
          apply (H1 y).
          apply H4.
          lia.
          rewrite <- H5.
          apply (H0 y).
      intros n.
      intro.
      intros m.
      constructor.
      unfold m.
      apply (H n H3).
      intros i.
      intro.
      assert (first_nat p n <= i).
        apply (H2 n i H4).
      lia.
    Qed.

  End NaturalNumber.

  Section CantorPairing.

    Fixpoint sum_from_0_to (n : nat) : nat :=
      match n with
      | 0 => 0
      | S n' => n + sum_from_0_to n'
      end
    .

    Proposition value_of_sum_from_0_to :
      forall n : nat,
      2 * sum_from_0_to n = n * (S n).
    Proof.
      intros n.
      induction n.
      - intuition.
      - simpl in *.
        lia.
    Qed.

    Fixpoint mapsLineToPlane (n : nat) : (nat * nat) :=
      match n with
      | 0 => (0, 0)
      | S n' =>
        let x := fst (mapsLineToPlane n') in
        let y := snd (mapsLineToPlane n') in
        match x with
        | 0 => (S y, 0)
        | S x' => (x', S y)
        end
      end
    .

    Proposition mapsLineToPlane_is_surjective:
      forall x y : nat,
      (x, y) = mapsLineToPlane (sum_from_0_to (x + y) + y).
    Proof.
      cut (
        forall z x y : nat,
        z = x + y ->
        (x, y) = mapsLineToPlane (sum_from_0_to z + y)
      ).
        intro.
        intros x y.
        apply (H (x + y) x y eq_refl).
      intros z.
      induction z.
      - intros x y.
        intro.
        assert (x = 0).
          lia.
        assert (y = 0).
          lia.
        subst.
        intuition.
      - cut (
          forall y x : nat,
          S z = x + y ->
          (x, y) = mapsLineToPlane (sum_from_0_to (S z) + y)
        ).
          intuition.
        intros y.
        induction y.
        * intros x.
          intro.
          assert (x = S z).
            lia.
          subst.
          simpl sum_from_0_to.
          simpl plus.
          assert ((0, z) = mapsLineToPlane (sum_from_0_to z + z)).
            apply (IHz 0 z).
            lia.
          assert ((0, z) = mapsLineToPlane (z + sum_from_0_to z + 0)).
            rewrite H0.
            assert (sum_from_0_to z + z = z + sum_from_0_to z + 0).
              lia.
            rewrite H1.
            tauto.
          simpl.
          rewrite <- H1.
          simpl.
          tauto.
        * intros x.
          intro.
          assert ((S x, y) = mapsLineToPlane (sum_from_0_to (S z) + y)).
            apply (IHy (S x)).
            lia.
          assert (mapsLineToPlane (z + sum_from_0_to z + S y) = mapsLineToPlane (sum_from_0_to (S z) + y)).
            assert (z + sum_from_0_to z + S y = sum_from_0_to (S z) + y).
              simpl.
              lia.
            rewrite H1.
            tauto.
          simpl.
          rewrite H1.
          rewrite <- H0.
          simpl.
          tauto.
    Qed.

    Proposition mapsLineToPlane_is_injective :
      forall n x y : nat,
      (x, y) = mapsLineToPlane n ->
      n = sum_from_0_to (x + y) + y.
    Proof.
      intros n.
      induction n.
      - intros x y.
        simpl.
        intro.
        assert (x = 0 /\ y = 0).
          apply (pair_equal_spec).
          apply H.
        destruct H0.
        subst.
        simpl.
        tauto.
      - cut (
          forall y x : nat,
          (x, y) = mapsLineToPlane (S n) ->
          S n = sum_from_0_to (x + y) + y
        ).
          intuition.
        intros y.
        destruct y.
        * intros x.
          intro.
          simpl in H.
          assert (mapsLineToPlane n = (fst (mapsLineToPlane n), snd (mapsLineToPlane n))).
            apply (surjective_pairing).
          destruct (fst (mapsLineToPlane n)). 
          + assert (x = S (snd (mapsLineToPlane n))).
              apply (proj1 (proj1 (pair_equal_spec _ _ 0 0) H)).
            subst.
            simpl.
            cut (n = snd (mapsLineToPlane n) + 0 + sum_from_0_to (snd (mapsLineToPlane n) + 0) + 0).
              lia.
            cut (n = sum_from_0_to (0 + snd (mapsLineToPlane n)) + snd (mapsLineToPlane n)).
              assert (snd (mapsLineToPlane n) + 0 = 0 + snd (mapsLineToPlane n)).
                lia.
              rewrite H1.
              lia.
            apply (IHn 0 (snd (mapsLineToPlane n))).
            rewrite <- H0.
            tauto.
          + assert (0 = S (snd (mapsLineToPlane n))).
              apply (proj2 (proj1 (pair_equal_spec x n0 _ _) H)).
            inversion H1.
        * intros x.
          intro.
          assert (x = fst (mapsLineToPlane (S n)) /\ S y = snd (mapsLineToPlane (S n))).
            apply pair_equal_spec.
            rewrite H.
            apply surjective_pairing.
          cut (n = sum_from_0_to (S x + y) + y).
            intro.
            assert (x + S y = S (x + y)).
              lia.
            rewrite H2.
            simpl in *.
            lia.
          apply (IHn (S x) y).
          assert (mapsLineToPlane n = (fst (mapsLineToPlane n), snd (mapsLineToPlane n))).
            apply (surjective_pairing).
          simpl in *.
          destruct (fst (mapsLineToPlane n)).
          + assert (S y = 0).
              destruct H0.
              simpl in H2.
              apply H2.
            inversion H2.
          + assert (x = n0 /\ y = snd (mapsLineToPlane n)).
              destruct H0.
              simpl in *.
              constructor.
              apply H0.
              inversion H2.
              tauto.
            destruct H2.
            rewrite <- H2 in *.
            rewrite H3 in *.
            rewrite <- H1.
            tauto.
    Qed.

  End CantorPairing.

  Section Ensembles.

    Definition Ensemble (A : Type) : Type :=
      A -> Prop
    .

    Definition member {A : Type} (x : A) (xs : Ensemble A) : Prop :=
      xs x
    .

    Definition isSubsetOf {A : Type} (xs1 : Ensemble A) (xs2 : Ensemble A) : Prop :=
      forall x : A, member x xs1 -> member x xs2
    .

    Inductive empty {A : Type} : Ensemble A :=
    .

    Inductive singleton {A : Type} : A -> Ensemble A :=
    | Singleton :
      forall x : A,
      member x (singleton x)
    .

    Inductive union {A : Type} : Ensemble A -> Ensemble A -> Ensemble A :=
    | UnionL :
      forall xs1 : Ensemble A,
      forall xs2 : Ensemble A,
      forall x : A,
      member x xs1 ->
      member x (union xs1 xs2)
    | UnionR :
      forall xs1 : Ensemble A,
      forall xs2 : Ensemble A,
      forall x : A,
      member x xs2 ->
      member x (union xs1 xs2)
    .

    Definition insert {A : Type} (x1 : A) (xs2 : Ensemble A) : Ensemble A :=
      union xs2 (singleton x1)
    .

    Definition intersection {A : Type} (xs1 : Ensemble A) (xs2 : Ensemble A) : Ensemble A :=
      fun x : A => member x xs1 /\ member x xs2
    .

    Definition difference {A : Type} (xs1 : Ensemble A) (xs2 : Ensemble A) : Ensemble A :=
      fun x : A => member x xs1 /\ ~ member x xs2
    .

    Definition delete {A : Type} (x1 : A) (xs2 : Ensemble A) : Ensemble A :=
      fun x : A => member x (difference xs2 (singleton x1))
    .

    Lemma isSubsetOf_insert {A : Type} :
      forall x1 : A,
      forall xs2 : Ensemble A,
      forall xs3 : Ensemble A,
      isSubsetOf xs2 xs3 ->
      isSubsetOf (insert x1 xs2) (insert x1 xs3).
    Proof.
      intros x1 xs2 xs3.
      intro.
      intros x.
      intro.
      inversion H0.
      subst.
      apply UnionL.
      apply H.
      apply H1.
      subst.
      apply UnionR.
      apply H1.
    Qed.

    Lemma subset_append {A : Type} :
      forall xs1 : list A,
      forall xs2 : list A,
      forall xs : Ensemble A,
      (forall x : A, In x xs1 -> member x xs) ->
      (forall x : A, In x xs2 -> member x xs) ->
      (forall x : A, In x (xs1 ++ xs2) -> member x xs).
    Proof.
      intros xs1 xs2 xs.
      intro.
      intro.
      intros x.
      intro.
      destruct (in_app_or xs1 xs2 x H1).
      apply (H x H2).
      apply (H0 x H2).
    Qed.

    Lemma in_append_iff_member_union {A : Type} :
      forall xs1 : list A,
      forall xs2 : list A,
      forall xs1' : Ensemble A,
      forall xs2' : Ensemble A,
      (forall x : A, In x xs1 <-> member x xs1') ->
      (forall x : A, In x xs2 <-> member x xs2') ->
      (forall x : A, In x (xs1 ++ xs2) <-> member x (union xs1' xs2')).
    Proof.
      intros xs1 xs2 xs1' xs2'.
      intro.
      intro.
      intros x.
      constructor.
      intro.
      destruct (in_app_or xs1 xs2 x H1).
      apply UnionL.
      apply (proj1 (H x) H2).
      apply UnionR.
      apply (proj1 (H0 x) H2).
      intro.
      inversion H1.
      subst.
      apply in_or_app.
      apply or_introl.
      apply (proj2 (H x) H2).
      subst.
      apply in_or_app.
      apply or_intror.
      apply (proj2 (H0 x) H2).
    Qed.

    Lemma subset_remove {A : Type} :
      forall eq_dec : (forall x1 : A, forall x2 : A, {x1 = x2} + {x1 <> x2}),
      forall x1 : A,
      forall xs2 : list A,
      forall xs : Ensemble A,
      (forall x : A, In x xs2 -> member x (insert x1 xs)) ->
      (forall x : A, In x (remove eq_dec x1 xs2) -> member x xs).
    Proof.
      intros eq_dec x1 xs2 xs.
      intro.
      intros x.
      intro.
      destruct (in_remove eq_dec xs2 x x1 H0).
      assert (member x (insert x1 xs)).
        apply (H x H1).
      inversion H3.
      subst.
      apply H4.
      subst.
      inversion H4.
      subst.
      tauto.
    Qed.
    
    Lemma in_remove_iff_member_delete {A : Type} :
      forall eq_dec : (forall x1 : A, forall x2 : A, {x1 = x2} + {x1 <> x2}),
      forall x1 : A,
      forall xs2 : list A,
      forall xs2' : Ensemble A,
      (forall x : A, In x xs2 <-> member x xs2') ->
      (forall x : A, In x (remove eq_dec x1 xs2) <-> member x (delete x1 xs2')).
    Proof.
      intros eq_dec x1 xs2 xs2'.
      intro.
      intros x.
      constructor.
      intro.
      destruct (in_remove eq_dec xs2 x x1 H0).
      constructor.
      apply (proj1 (H x) H1).
      intro.
      inversion H3.
      subst.
      tauto.
      intro.
      destruct H0.
      apply in_in_remove.
      intro.
      apply H1.
      subst.
      apply Singleton.
      apply (proj2 (H x) H0).
    Qed.

  End Ensembles.

End Helper.

Module CountableBooleanAlgebra.

  Import ListNotations.

  Import Helper.

  Section DefinitionOfCBA.

    Class CountableBooleanAlgebra (B : Type) : Type :=
      { eqB : B -> B -> Prop
      ; trueB : B
      ; falseB : B
      ; negB : B -> B
      ; andB : B -> B -> B
      ; orB : B -> B -> B
      ; enumB : nat -> B
      ; eqB_refl : forall b1 : B, eqB b1 b1
      ; eqB_symm : forall b1 : B, forall b2 : B, eqB b1 b2 -> eqB b2 b1
      ; eqB_trans : forall b1 : B, forall b2 : B, forall b3 : B, eqB b1 b2 -> eqB b2 b3 -> eqB b1 b3
      ; trueB_preserves_eqB : eqB trueB trueB
      ; falseB_preserves_eqB : eqB falseB falseB
      ; negB_preserves_eqB : forall b1 : B, forall b1' : B, eqB b1 b1' -> eqB (negB b1) (negB b1')
      ; andB_preserves_eqB : forall b1 : B, forall b1' : B, forall b2 : B, forall b2' : B, eqB b1 b1' -> eqB b2 b2' -> eqB (andB b1 b2) (andB b1' b2')
      ; or_preserves_eqB : forall b1 : B, forall b1' : B, forall b2 : B, forall b2' : B, eqB b1 b1' -> eqB b2 b2' -> eqB (orB b1 b2) (orB b1' b2')
      ; andB_associative : forall b1 : B, forall b2 : B, forall b3 : B, eqB (andB b1 (andB b2 b3)) (andB (andB b1 b2) b3)
      ; orB_associative : forall b1 : B, forall b2 : B, forall b3 : B, eqB (orB b1 (orB b2 b3)) (orB (orB b1 b2) b3)
      ; andB_idempotent : forall b1 : B, eqB (andB b1 b1) b1
      ; orB_idempotent : forall b1 : B, eqB (orB b1 b1) b1
      ; andB_commutative : forall b1 : B, forall b2 : B, eqB (andB b1 b2) (andB b2 b1)
      ; orB_commutative : forall b1 : B, forall b2 : B, eqB (orB b1 b2) (orB b2 b1)
      ; andB_distribute_orB : forall b1 : B, forall b2 : B, forall b3 : B, eqB (andB b1 (orB b2 b3)) (orB (andB b1 b2) (andB b1 b3))
      ; orB_distribute_andB : forall b1 : B, forall b2 : B, forall b3 : B, eqB (orB b1 (andB b2 b3)) (andB (orB b1 b2) (orB b1 b3))
      ; absorption_andB_orB : forall b1 : B, forall b2 : B, eqB (andB b1 (orB b1 b2)) b1
      ; absorption_orB_andB : forall b1 : B, forall b2 : B, eqB (orB b1 (andB b1 b2)) b1
      ; falseB_zero_andB : forall b1 : B, eqB (andB b1 falseB) falseB
      ; trueB_zero_orB : forall b1 : B, eqB (orB b1 trueB) trueB
      ; falseB_unit_orB : forall b1 : B, eqB (orB b1 falseB) b1
      ; trueB_unit_andB : forall b1 : B, eqB (andB b1 trueB) b1
      ; andB_negB : forall b1 : B, eqB (andB b1 (negB b1)) falseB
      ; orB_negB : forall b1 : B, eqB (orB b1 (negB b1)) trueB 
      ; enumB_surjective : forall b : B, exists n : nat, enumB n = b
      }
    .

  End DefinitionOfCBA.

  Section TheoryOfCBA.

    Variable B : Type.

    Variable cba : CountableBooleanAlgebra B.

    Notation "b1 == b2" := (eqB b1 b2) (at level 80).

    Notation "b1 =< b2" := (eqB (andB b1 b2) b1) (at level 80).

    Lemma leq_CBA_refl :
      forall b1 : B,
      b1 =< b1.
    Proof.
      intros b1.
      apply andB_idempotent.
    Qed.

    Lemma leq_CBA_refl' :
      forall b1 : B,
      forall b2 : B,
      b1 == b2 ->
      b1 =< b2.
    Proof.
      intros b1 b2 H.
      apply eqB_symm.
      apply (eqB_trans b1 (andB b1 b1) (andB b1 b2)).
      apply eqB_symm.
      apply andB_idempotent.
      apply andB_preserves_eqB.
      apply eqB_refl.
      apply H.
    Qed.

    Lemma leq_CBA_asym :
      forall b1 : B,
      forall b2 : B,
      b1 =< b2 ->
      b2 =< b1 ->
      b1 == b2.
    Proof.
      intros b1 b2 H1 H2.
      apply (eqB_trans b1 (andB b1 b2) b2).
      apply eqB_symm.
      apply H1.
      apply (eqB_trans (andB b1 b2) (andB b2 b1) b2).
      apply andB_commutative.
      apply H2.
    Qed.

    Lemma leq_CBA_trans :
      forall b1 : B,
      forall b2 : B,
      forall b3 : B,
      b1 =< b2 ->
      b2 =< b3 ->
      b1 =< b3.
    Proof.
      intros b1 b2 b3 H1 H2.
      apply (eqB_trans (andB b1 b3) (andB (andB b1 b2) b3) b1).
      apply andB_preserves_eqB.
      apply eqB_symm.
      apply H1.
      apply eqB_refl.
      apply eqB_symm.
      apply (eqB_trans b1 (andB b1 (andB b2 b3)) (andB (andB b1 b2) b3)).
      apply (eqB_trans b1 (andB b1 b2) (andB b1 (andB b2 b3))).
      apply eqB_symm.
      apply H1.
      apply andB_preserves_eqB.
      apply eqB_refl.
      apply eqB_symm.
      apply H2.
      apply andB_associative.
    Qed.

    Lemma leq_CBA_andB :
      forall b1 : B,
      forall b1' : B,
      forall b2 : B,
      forall b2' : B,
      b1 =< b2 ->
      b1' =< b2' ->
      andB b1 b1' =< andB b2 b2'.
    Proof.
      intros b1 b1' b2 b2' H1 H2.
      assert (andB b1 b1' =< andB b2 b1').
        apply eqB_symm.
        apply (eqB_trans (andB b1 b1') (andB (andB b1 b2) b1') (andB (andB b1 b1') (andB b2 b1'))).
        apply andB_preserves_eqB.
        apply eqB_symm.
        apply H1.
        apply eqB_refl.
        apply (eqB_trans (andB (andB b1 b2) b1') (andB b1 (andB b2 b1')) (andB (andB b1 b1') (andB b2 b1'))).
        apply eqB_symm.
        apply andB_associative.
        apply (eqB_trans (andB b1 (andB b2 b1')) (andB b1 (andB b1' (andB b2 b1'))) (andB (andB b1 b1') (andB b2 b1'))).
        apply andB_preserves_eqB.
        apply eqB_refl.
        apply (eqB_trans (andB b2 b1') (andB b2 (andB b1' b1')) (andB b1' (andB b2 b1'))).
        apply andB_preserves_eqB.
        apply eqB_refl.
        apply eqB_symm.
        apply leq_CBA_refl.
        apply eqB_symm.
        apply (eqB_trans (andB b1' (andB b2 b1')) (andB (andB b2 b1') b1') (andB b2 (andB b1' b1'))).
        apply (eqB_trans (andB b1' (andB b2 b1')) (andB (andB b1' b2) b1') (andB (andB b2 b1') b1')).
        apply andB_associative.
        apply andB_preserves_eqB.
        apply andB_commutative.
        apply eqB_refl.
        apply eqB_symm.
        apply andB_associative.
        apply andB_associative.
      assert (andB b2 b1' =< andB b2 b2').
        apply eqB_symm.
        apply (eqB_trans (andB b2 b1') (andB b2 (andB b1' b2')) (andB (andB b2 b1') (andB b2 b2'))).
        apply andB_preserves_eqB.
        apply eqB_refl.
        apply eqB_symm.
        apply H2.
        apply (eqB_trans (andB b2 (andB b1' b2')) (andB (andB b2 b2) (andB b1' b2')) (andB (andB b2 b1') (andB b2 b2'))).
        apply andB_preserves_eqB.
        apply eqB_symm.
        apply leq_CBA_refl.
        apply eqB_refl.
        apply (eqB_trans (andB (andB b2 b2) (andB b1' b2')) (andB b2 (andB b2 (andB b1' b2'))) (andB (andB b2 b1') (andB b2 b2'))).
        apply eqB_symm.
        apply andB_associative.
        apply (eqB_trans (andB b2 (andB b2 (andB b1' b2'))) (andB b2 (andB (andB b2 b1') b2')) (andB (andB b2 b1') (andB b2 b2'))).
        apply andB_preserves_eqB.
        apply eqB_refl.
        apply andB_associative.
        apply (eqB_trans (andB b2 (andB (andB b2 b1') b2')) (andB b2 (andB (andB b1' b2) b2')) (andB (andB b2 b1') (andB b2 b2'))).
        apply andB_preserves_eqB.
        apply eqB_refl.
        apply andB_preserves_eqB.
        apply andB_commutative.
        apply eqB_refl.
        apply (eqB_trans (andB b2 (andB (andB b1' b2) b2')) (andB b2 (andB b1' (andB b2 b2'))) (andB (andB b2 b1') (andB b2 b2'))).
        apply andB_preserves_eqB.
        apply eqB_refl.
        apply eqB_symm.
        apply andB_associative.
        apply andB_associative.
        apply (leq_CBA_trans (andB b1 b1') (andB b2 b1') (andB b2 b2') H H0).
    Qed.

    Lemma andBs_CBA :
      forall ps1 : list B,
      forall ps2 : list B,
      fold_right andB trueB (ps1 ++ ps2) == andB (fold_right andB trueB ps1) (fold_right andB trueB ps2).
    Proof.
      intros ps1.
      induction ps1.
      - intros ps.
        simpl.
        apply eqB_symm.
        apply (eqB_trans (andB trueB (fold_right andB trueB ps)) (andB (fold_right andB trueB ps) trueB) (fold_right andB trueB ps)).
        apply andB_commutative.
        apply trueB_unit_andB.
      - intros ps2.
        simpl.
        apply (eqB_trans (andB a (fold_right andB trueB (ps1 ++ ps2))) (andB a (andB (fold_right andB trueB ps1) (fold_right andB trueB ps2))) (andB (andB a (fold_right andB trueB ps1)) (fold_right andB trueB ps2))).
        apply andB_preserves_eqB.
        apply eqB_refl.
        apply IHps1.
        apply andB_associative.
    Qed.

    Definition isFilter (filter : Ensemble B) : Prop :=
      (exists b0 : B, member b0 filter) /\ (forall b1 : B, forall b2 : B, member b1 filter -> b1 =< b2 -> member b2 filter) /\ (forall b1 : B, forall b2 : B, forall b : B, member b1 filter -> member b2 filter -> b == andB b1 b2 -> member b filter)
    .

    Lemma isFilter_refl' :
      forall bs1 : Ensemble B,
      isFilter bs1 ->
      forall bs2 : Ensemble B,
      isSubsetOf bs1 bs2 ->
      isSubsetOf bs2 bs1 ->
      isFilter bs2.
    Proof.
      intros bs1 H0 bs2 H1 H2.
      destruct H0.
      destruct H0.
      constructor.
      destruct H as [b1].
      exists b1.
      apply (H1 b1 H).
      constructor.
      intros b1 b2 H4 H5.
      apply (H1 b2).
      apply (H0 b1 b2).
      apply (H2 b1 H4).
      apply H5.
      intros b1 b2 b H4 H5 H6.
      apply (H1 b).
      apply (H3 b1 b2 b).
      apply (H2 b1 H4).
      apply (H2 b2 H5).
      apply H6.
    Qed.

    Inductive Cl : Ensemble B -> Ensemble B :=
    | Closure :
      forall ps : list B,
      forall b : B,
      forall bs : Ensemble B,
      (forall p : B, In p ps -> member p bs) ->
      fold_right andB trueB ps =< b ->
      member b (Cl bs)
    .

    Definition inconsistent (bs1 : Ensemble B) : Prop :=
      exists b : B, member b bs1 /\ b == falseB
    .

    Definition equiconsistent (bs1 : Ensemble B) (bs2 : Ensemble B) : Prop :=
      inconsistent bs1 <-> inconsistent bs2
    .
    
    Definition isElementComplete (bs1 : Ensemble B) (b2 : B) : Prop :=
      equiconsistent bs1 (Cl (insert b2 bs1)) -> member b2 bs1
    .

    Definition isComplete (bs1 : Ensemble B) : Prop :=
      forall b2 : B, isElementComplete bs1 b2
    .

    Lemma inconsistent_subset :
      forall bs1 : Ensemble B,
      forall bs2 : Ensemble B,
      isSubsetOf bs1 bs2 ->
      inconsistent bs1 ->
      inconsistent bs2.
    Proof.
      intros bs1 bs2.
      intro.
      intro.
      destruct H0 as [b'].
      destruct H0.
      exists b'.
      constructor.
      apply (H b' H0).
      apply H1.
    Qed.

    Lemma fact_1_of_1_2_8 :
      forall bs : Ensemble B,
      isFilter (Cl bs).
    Proof.
      intros bs.
      constructor.
      exists trueB.
      apply (Closure []).
      intros p.
      intro.
      inversion H.
      simpl.
      apply leq_CBA_refl.
      constructor.
      intros b1 b H1 H2.
      inversion H1.
      subst.
      apply (Closure ps).
      apply H.
      apply (leq_CBA_trans (fold_right andB trueB ps) b1 b H0 H2).
      intros b1 b2 b H1 H2 H3.
      destruct H1.
      destruct H2.
      apply (Closure (ps ++ ps0)).
      intros p.
      intro.
      destruct (in_app_or ps ps0 p H4).
      apply (H p H5).
      apply (H1 p H5).
      assert (fold_right andB trueB (ps ++ ps0) == andB (fold_right andB trueB ps) (fold_right andB trueB ps0)).
        apply andBs_CBA.
      apply (leq_CBA_trans (fold_right andB trueB (ps ++ ps0)) (andB b0 b1) b).
      apply (leq_CBA_trans (fold_right andB trueB (ps ++ ps0)) (andB (fold_right andB trueB ps) (fold_right andB trueB ps0)) (andB b0 b1)).
      apply (leq_CBA_refl' (fold_right andB trueB (ps ++ ps0)) (andB (fold_right andB trueB ps) (fold_right andB trueB ps0)) H4).
      apply (leq_CBA_andB (fold_right andB trueB ps) (fold_right andB trueB ps0) b0 b1).
      apply H0.
      apply H2.
      apply (leq_CBA_refl' (andB b0 b1) b).
      apply eqB_symm.
      apply H3.
    Qed.

    Lemma fact_2_of_1_2_8 :
      forall bs : Ensemble B,
      isFilter bs ->
      member trueB bs.
    Proof.
      intros bs.
      intro.
      destruct H.
      destruct H0.
      destruct H as [b].
      apply (H0 b trueB).
      apply H.
      apply trueB_unit_andB.
    Qed.

    Lemma fact_3_of_1_2_8 :
      forall bs : Ensemble B,
      isSubsetOf bs (Cl bs).
    Proof.
      intros bs.
      intros b.
      intro.
      apply (Closure [b]).
      intros p.
      intro.
      inversion H0.
      subst.
      apply H.
      inversion H1.
      simpl.
      apply leq_CBA_refl'.
      apply trueB_unit_andB.
    Qed.

    Lemma fact_4_of_1_2_8 :
      forall bs1 : Ensemble B,
      forall bs2 : Ensemble B,
      isSubsetOf bs1 bs2 ->
      isSubsetOf (Cl bs1) (Cl bs2).
    Proof.
      intros bs1 bs2.
      intro.
      intros b.
      intro.
      destruct H0.
      apply (Closure ps).
      intros p.
      intro.
      apply (H p).
      apply (H0 p H2).
      apply H1.
    Qed.

    Lemma fact_5_of_1_2_8 :
      forall bs : Ensemble B,
      isFilter bs ->
      isSubsetOf (Cl bs) bs.
    Proof.
      intros bs.
      intro.
      destruct H.
      destruct H0.
      cut (
        forall ps : list B,
        (forall b : B, In b ps -> member b bs) ->
        member (fold_right andB trueB ps) bs
      ).
        intro.
        intros p.
        intro.
        destruct H3.
        apply (H0 (fold_right andB trueB ps) b).
        apply H2.
        apply H3.
        apply H4.
      intros ps.
      induction ps.
      - intro.
        simpl in *.
        destruct H as [b'].
        apply (H0 b' trueB).
        apply H.
        apply trueB_unit_andB.
      - intro.
        simpl in *.
        apply (H1 a (fold_right andB trueB ps) (andB a (fold_right andB trueB ps))).
        apply (H2 a).
        tauto.
        apply IHps.
        intros b.
        intro.
        apply H2.
        tauto.
        apply eqB_refl.
    Qed.

    Lemma proposition_1_of_1_2_9 :
      forall bs : Ensemble B,
      isFilter bs ->
      forall b1 : B,
      member b1 bs ->
      forall b2 : B,
      b1 == b2 ->
      member b2 bs.
    Proof.
      intros bs.
      intro.
      destruct H.
      destruct H0.
      intros b1.
      intro.
      intros b2.
      intro.
      apply (H0 b1 b2).
      apply H2.
      apply leq_CBA_refl'.
      apply H3.
    Qed.

    Inductive Insert : Ensemble B -> nat -> Ensemble B :=
    | Insertion :
      forall bs : Ensemble B,
      forall n : nat,
      equiconsistent bs (Cl (insert (enumB n) bs)) ->
      member (enumB n) (Insert bs n)
    .

    Fixpoint improveFilter (bs : Ensemble B) (n : nat) : Ensemble B :=
      match n with
      | 0 => bs
      | S n' =>
        let bs' : Ensemble B := improveFilter bs n' in
        Cl (union bs' (Insert bs' n'))
      end
    .

    Lemma lemma_1_of_1_2_11 :
      forall bs : Ensemble B,
      isFilter bs ->
      forall n : nat,
      isFilter (improveFilter bs n).
    Proof.
      intros bs.
      intro.
      intros n.
      induction n.
      - simpl.
        apply H.
      - simpl.
        apply fact_1_of_1_2_8.
    Qed.

    Lemma lemma_1_of_1_2_12 :
      forall bs : Ensemble B,
      forall n1 : nat,
      forall n2 : nat,
      n1 <= n2 ->
      isSubsetOf (improveFilter bs n1) (improveFilter bs n2).
    Proof.
      intros bs n1 n2.
      intro.
      induction H.
      - unfold isSubsetOf.
        intuition.
      - assert (isSubsetOf (improveFilter bs m) (improveFilter bs (S m))).
          assert (isSubsetOf (union (improveFilter bs m) (Insert (improveFilter bs m) m)) (Cl (union (improveFilter bs m) (Insert (improveFilter bs m) m)))).
            apply fact_3_of_1_2_8.
          intros p.
          intro.
          apply H0.
          apply UnionL.
          apply H1.
        intros p.
        intro.
        apply H0.
        apply IHle.
        apply H1.
    Qed.

    Lemma lemma_1_of_1_2_13 :
      forall bs : Ensemble B,
      isFilter bs ->
      forall n : nat,
      equiconsistent bs (improveFilter bs n).
    Proof.
      intros bs.
      intro HHH.
      intros n.
      induction n.
      - simpl.
        unfold equiconsistent.
        intuition.
      - constructor.
        unfold inconsistent.
        intro.
        destruct H as [b'].
        destruct H.
        exists b'.
        constructor.
        apply (lemma_1_of_1_2_12 bs 0 (S n)).
        lia.
        simpl.
        apply H.
        apply H0.
        intro.
        cut (
          forall ps : list B,
          (forall p : B, In p ps -> member p (union (improveFilter bs n) (Insert (improveFilter bs n) n))) ->
          member (fold_right andB trueB ps) (improveFilter bs n) \/ (exists p' : B, In p' ps /\ member p' (Insert (improveFilter bs n) n))
        ).
          intro.
          destruct H as [b'].
          destruct H.
          inversion H.
          subst.
          destruct (H0 ps H2).
          apply (proj2 IHn).
          exists (fold_right andB trueB ps).
          constructor.
          apply H4.
          apply leq_CBA_asym.
          apply (leq_CBA_trans (fold_right andB trueB ps) b' falseB).
          apply H3.
          apply leq_CBA_refl'.
          apply H1.
          apply (eqB_trans (andB falseB (fold_right andB trueB ps)) (andB (fold_right andB trueB ps) falseB) falseB).
          apply andB_commutative.
          apply falseB_zero_andB.
          destruct H4 as [p'].
          destruct H4.
          assert (member p' (union (improveFilter bs n) (Insert (improveFilter bs n) n))).
            apply (H2 p' H4).
          assert (member falseB (Cl (union (improveFilter bs n) (Insert (improveFilter bs n) n)))).
            apply (Closure ps).
            apply H2.
            apply (leq_CBA_trans (fold_right andB trueB ps) b' falseB).
            apply H3.
            apply leq_CBA_refl'.
            apply H1.
          inversion H5.
          subst.
          apply (proj2 IHn).
          apply (proj2 H8).
          exists falseB.
          constructor.
          assert (isSubsetOf (union (improveFilter bs n) (Insert (improveFilter bs n) n)) (insert (enumB n) (improveFilter bs n))).
            intros p.
            intro.
            inversion H9.
            subst.
            apply UnionL.
            apply H10.
            subst.
            inversion H10.
            subst.
            apply UnionR.
            apply Singleton.
          assert (isSubsetOf (Cl (union (improveFilter bs n) (Insert (improveFilter bs n) n))) (Cl (insert (enumB n) (improveFilter bs n)))).
            apply fact_4_of_1_2_8.
            apply H9.
          apply H10.
          apply H7.
          apply eqB_refl.
        intros ps.
        induction ps.
        * simpl in *.
          intro.
          apply or_introl.
          apply fact_2_of_1_2_8.
          apply lemma_1_of_1_2_11.
          apply HHH.
        * simpl in *.
          intro.
          assert (
            forall p : B,
            In p ps ->
            member p (union (improveFilter bs n) (Insert (improveFilter bs n) n))
          ).
            intros p.
            intro.
            apply (H0 p).
            tauto.
          assert (member a (union (improveFilter bs n) (Insert (improveFilter bs n) n))).
            apply H0.
            tauto.
          assert (isFilter (improveFilter bs n)).
            apply lemma_1_of_1_2_11.
            apply HHH.
          destruct (IHps H1).
          inversion H2.
          subst.
          destruct H3.
          destruct H6.
          apply or_introl.
          apply (H7 a (fold_right andB trueB ps)).
          apply H5.
          apply H4.
          apply eqB_refl.
          subst.
          apply or_intror.
          exists a.
          tauto.
          apply or_intror.
          destruct H4 as [p'].
          exists p'.
          destruct H4.
          constructor.
          tauto.
          apply H5.
    Qed.

    Lemma lemma_2_of_1_2_13 :
      forall bs : Ensemble B,
      isFilter bs ->
      forall n1 : nat,
      forall n2 : nat,
      equiconsistent (improveFilter bs n1) (improveFilter bs n2).
    Proof.
      intros bs HHH n1 n2.
      assert (equiconsistent bs (improveFilter bs n1)).
        apply lemma_1_of_1_2_13.
        apply HHH.
      assert (equiconsistent bs (improveFilter bs n2)).
        apply lemma_1_of_1_2_13.
        apply HHH.
      unfold equiconsistent in *.
      intuition.
    Qed.

    Inductive CompleteFilter : Ensemble B -> Ensemble B :=
    | InCompleteFilter :
      forall n : nat,
      forall bs : Ensemble B,
      forall b : B,
      member b (improveFilter bs n) ->
      member b (CompleteFilter bs)
    .

    Lemma lemma_3_of_1_2_13 :
      forall bs : Ensemble B,
      isFilter bs ->
      equiconsistent bs (CompleteFilter bs).
    Proof.
      intros bs HHH.
      constructor.
      intro.
      destruct H as [p'].
      destruct H.
      exists p'.
      constructor.
      apply (InCompleteFilter 0).
      simpl.
      apply H.
      apply H0.
      intro.
      destruct H as [p'].
      destruct H.
      inversion H.
      subst.
      assert (equiconsistent bs (improveFilter bs n)).
        apply lemma_1_of_1_2_13.
        apply HHH.
      apply (proj2 H2).
      exists p'.
      tauto.
    Qed.

    Theorem theorem_1_2_14 :
      forall bs : Ensemble B,
      isFilter bs ->
      isSubsetOf bs (CompleteFilter bs) /\ isFilter (CompleteFilter bs) /\ isComplete (CompleteFilter bs) /\ equiconsistent bs (CompleteFilter bs).
    Proof.
      intros bs HHH.
      assert (isSubsetOf bs (CompleteFilter bs)).
        intros p.
        intro.
        apply (InCompleteFilter 0).
        simpl.
        apply H.
      constructor.
      apply H.
      constructor.
      inversion HHH.
      destruct H0 as [b0].
      constructor.
      exists b0.
      apply H.
      apply H0.
      constructor.
      intros b1 b2.
      intro.
      intro.
      inversion H2.
      subst.
      assert (isFilter (improveFilter bs n)).
        apply lemma_1_of_1_2_11.
        apply HHH.
      destruct H5.
      destruct H6.
      apply (InCompleteFilter n).
      apply (H6 b1 b2 H4 H3).
      intros b1 b2 b.
      intro.
      intro.
      intro.
      inversion H2.
      subst.
      inversion H3.
      subst.
      assert (n >= n0 \/ n0 >= n).
        lia.
      destruct H7.
      assert (isFilter (improveFilter bs n)).
        apply lemma_1_of_1_2_11.
        apply HHH.
      destruct H8.
      destruct H9.
      apply (InCompleteFilter n).
      apply (H10 b1 b2 b).
      apply H5.
      assert (isSubsetOf (improveFilter bs n0) (improveFilter bs n)).
        apply lemma_1_of_1_2_12.
        lia.
      apply H11.
      apply H6.
      apply H4.
      assert (isFilter (improveFilter bs n0)).
        apply lemma_1_of_1_2_11.
        apply HHH.
      destruct H8.
      destruct H9.
      apply (InCompleteFilter n0).
      apply (H10 b1 b2 b).
      assert (isSubsetOf (improveFilter bs n) (improveFilter bs n0)).
        apply lemma_1_of_1_2_12.
        lia.
      apply H11.
      apply H5.
      apply H6.
      apply H4.
      constructor.
      intros b.
      intro.
      destruct (enumB_surjective b) as [n].
      cut (equiconsistent (improveFilter bs n) (Cl (union (improveFilter bs n) (singleton b)))).
        intro.
        apply (InCompleteFilter (S n)).
        simpl.
        apply (Closure [b]).
        intros p.
        intro.
        inversion H3.
        subst.
        apply UnionR.
        apply Insertion.
        apply H2.
        inversion H4.
        simpl.
        apply leq_CBA_refl'.
        apply trueB_unit_andB.
      constructor.
      intro.
      destruct H2 as [b'].
      destruct H2.
      exists b'.
      constructor.
      apply (Closure [b']).
      intros p.
      intro.
      inversion H4.
      subst.
      apply UnionL.
      apply H2.
      inversion H5.
      simpl.
      apply leq_CBA_refl'.
      apply trueB_unit_andB.
      apply H3.
      intro.
      cut (inconsistent (Cl (insert b (CompleteFilter bs)))).
        assert (equiconsistent bs (improveFilter bs n)).
          apply lemma_1_of_1_2_13.
          apply HHH.
        assert (equiconsistent bs (CompleteFilter bs)).
          apply lemma_3_of_1_2_13.
          apply HHH.
        unfold equiconsistent in *.
        tauto.
      destruct H2 as [b'].
      destruct H2.
      exists b'.
      constructor.
      assert (isSubsetOf (Cl (union (improveFilter bs n) (singleton b))) (Cl (insert b (CompleteFilter bs)))).
        apply fact_4_of_1_2_8.
        intros p.
        intro.
        inversion H4.
        subst.
        apply UnionL.
        apply (InCompleteFilter n).
        apply H5.
        subst.
        apply UnionR.
        apply H5.
      apply H4.
      apply H2.
      apply H3.
      apply lemma_3_of_1_2_13.
      apply HHH.
    Qed.

    Definition isUltraFilter (bs : Ensemble B) :=
      isFilter bs /\ (forall bs' : Ensemble B, isFilter bs' -> equiconsistent bs bs' -> isSubsetOf bs bs' -> isSubsetOf bs' bs)
    .

    Corollary corollary_1_2_16 :
      forall bs : Ensemble B,
      isFilter bs ->
      isUltraFilter (CompleteFilter bs).
    Proof.
      intros bs HHH.
      destruct (theorem_1_2_14 bs HHH).
      destruct H0.
      destruct H1.
      constructor.
      apply H0.
      intros bs' HHH'.
      intro.
      intro.
      intros b.
      intro.
      cut (
        equiconsistent (CompleteFilter bs) (Cl (insert b (CompleteFilter bs)))
      ).
        intro.
        apply H1.
        apply H6.
      constructor.
      intro.
      destruct H6 as [b'].
      destruct H6.
      exists b'.
      constructor.
      apply fact_3_of_1_2_8.
      apply UnionL.
      apply H6.
      apply H7.
      intro.
      apply (proj2 H3).
      assert (inconsistent (Cl (insert b bs'))).
        assert (isSubsetOf (insert b (CompleteFilter bs)) (insert b bs')).
          intros p.
          intro.
          inversion H7.
          subst.
          apply UnionL.
          apply H4.
          apply H8.
          subst.
          apply UnionR.
          apply H8.
        destruct H6 as [b'].
        destruct H6.
        exists b'.
        constructor.
        assert (isSubsetOf (Cl (insert b (CompleteFilter bs))) (Cl (insert b bs'))).
          apply fact_4_of_1_2_8.
          apply H7.
        apply H9.
        apply H6.
        apply H8.
      destruct H7 as [b'].
      destruct H7.
      exists b'.
      constructor.
      apply fact_5_of_1_2_8.
      apply HHH'.
      assert (isSubsetOf (Cl (insert b bs')) (Cl bs')).
        apply fact_4_of_1_2_8.
        intros p.
        intro.
        inversion H9.
        subst.
        apply H10.
        subst.
        inversion H10.
        subst.
        apply H5.
      apply H9.
      apply H7.
      apply H8.
    Qed.

  End TheoryOfCBA.

End CountableBooleanAlgebra.

Module PropositionalLogic.

  Import ListNotations.

  Import Helper.

  Import CountableBooleanAlgebra.

  Section Syntax.

    Definition PVar : Set := 
      nat
    .

    Inductive Formula : Set :=
    | AtomF : forall i : PVar, Formula
    | ContradictionF : Formula
    | NegationF : forall p1 : Formula, Formula
    | ConjunctionF : forall p1 : Formula, forall p2 : Formula, Formula
    | DisjunctionF : forall p1 : Formula, forall p2 : Formula, Formula
    | ImplicationF : forall p1 : Formula, forall p2 : Formula, Formula
    | BiconditionalF : forall p1 : Formula, forall p2 : Formula, Formula
    .

    Proposition eq_Formula_dec :
      forall p1 p2 : Formula,
      {p1 = p2} + {p1 <> p2}.
    Proof.
      intros p1.
      induction p1.
      - intros p2.
        destruct p2.
        * destruct (Nat.eq_dec i i0).
          + intuition.
          + assert (AtomF i <> AtomF i0).
              intro.
              inversion H.
              intuition.
            intuition.
        * assert (AtomF i <> ContradictionF).
            intro.
            inversion H.
          intuition.
        * assert (AtomF i <> NegationF p2).
            intro.
            inversion H.
          intuition.
        * assert (AtomF i <> ConjunctionF p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (AtomF i <> DisjunctionF p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (AtomF i <> ImplicationF p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (AtomF i <> BiconditionalF p2_1 p2_2).
            intro.
            inversion H.
          intuition.
      - intros p2.
        induction p2.
        * assert (ContradictionF <> AtomF i).
            intro.
            inversion H.
          intuition.
        * intuition.
        * assert (ContradictionF <> NegationF p2).
            intro.
            inversion H.
          intuition.
        * assert (ContradictionF <> ConjunctionF p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (ContradictionF <> DisjunctionF p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (ContradictionF <> ImplicationF p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (ContradictionF <> BiconditionalF p2_1 p2_2).
            intro.
            inversion H.
          intuition.
      - intros p2.
        destruct p2.
        * assert (NegationF p1 <> AtomF i).
            intro.
            inversion H.
          intuition.
        * assert (NegationF p1 <> ContradictionF).
            intro.
            inversion H.
          intuition.
        * destruct (IHp1 p2).
            subst.
            tauto.
            assert (NegationF p1 <> NegationF p2).
              intro.
              inversion H.
              apply (n H1).
            intuition.
        * assert (NegationF p1 <> ConjunctionF p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (NegationF p1 <> DisjunctionF p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (NegationF p1 <> ImplicationF p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (NegationF p1 <> BiconditionalF p2_1 p2_2).
            intro.
            inversion H.
          intuition.
      - intros p2.
        destruct p2.
        * assert (ConjunctionF p1_1 p1_2 <> AtomF i).
            intro.
            inversion H.
          intuition.
        * assert (ConjunctionF p1_1 p1_2 <> ContradictionF).
            intro.
            inversion H.
          intuition.
        * assert (ConjunctionF p1_1 p1_2 <> NegationF p2).
            intro.
            inversion H.
          intuition.
        * destruct (IHp1_1 p2_1).
            destruct (IHp1_2 p2_2).
              subst.
              intuition.
              assert (ConjunctionF p1_1 p1_2 <> ConjunctionF p2_1 p2_2).
                intro.
                inversion H.
                tauto.
              tauto.
            assert (ConjunctionF p1_1 p1_2 <> ConjunctionF p2_1 p2_2).
              intro.
              inversion H.
              tauto.
            tauto.
        * assert (ConjunctionF p1_1 p1_2 <> DisjunctionF p2_1 p2_2).
            intro.
            inversion H.
          tauto.
        * assert (ConjunctionF p1_1 p1_2 <> ImplicationF p2_1 p2_2).
            intro.
            inversion H.
          tauto.
        * assert (ConjunctionF p1_1 p1_2 <> BiconditionalF p2_1 p2_2).
            intro.
            inversion H.
          tauto.
      - intros p2.
        destruct p2.
        * assert (DisjunctionF p1_1 p1_2 <> AtomF i).
            intro.
            inversion H.
          tauto.
        * assert (DisjunctionF p1_1 p1_2 <> ContradictionF).
            intro.
            inversion H.
          tauto.
        * assert (DisjunctionF p1_1 p1_2 <> NegationF p2).
            intro.
            inversion H.
          tauto.
        * assert (DisjunctionF p1_1 p1_2 <> ConjunctionF p2_1 p2_2).
            intro.
            inversion H.
          tauto.
        * destruct (IHp1_1 p2_1).
            destruct (IHp1_2 p2_2).
              subst.
              intuition.
              assert (DisjunctionF p1_1 p1_2 <> DisjunctionF p2_1 p2_2).
                intro.
                inversion H.
                tauto.
              tauto.
            assert (DisjunctionF p1_1 p1_2 <> DisjunctionF p2_1 p2_2).
              intro.
              inversion H.
              tauto.
            tauto.
        * assert (DisjunctionF p1_1 p1_2 <> ImplicationF p2_1 p2_2).
            intro.
            inversion H.
          tauto.
        * assert (DisjunctionF p1_1 p1_2 <> BiconditionalF p2_1 p2_2).
            intro.
            inversion H.
          tauto.
      - intros p2.
        induction p2.
        * assert (ImplicationF p1_1 p1_2 <> AtomF i).
            intro.
            inversion H.
          tauto.
        * assert (ImplicationF p1_1 p1_2 <> ContradictionF).
            intro.
            inversion H.
          tauto.
        * assert (ImplicationF p1_1 p1_2 <> NegationF p2).
            intro.
            inversion H.
          tauto.
        * assert (ImplicationF p1_1 p1_2 <> ConjunctionF p2_1 p2_2).
            intro.
            inversion H.
          tauto.
        * assert (ImplicationF p1_1 p1_2 <> DisjunctionF p2_1 p2_2).
            intro.
            inversion H.
          tauto.
        * destruct (IHp1_1 p2_1).
            destruct (IHp1_2 p2_2).
              subst.
              intuition.
              assert (ImplicationF p1_1 p1_2 <> ImplicationF p2_1 p2_2).
                intro.
                inversion H.
                tauto.
              tauto.
            assert (ImplicationF p1_1 p1_2 <> ImplicationF p2_1 p2_2).
              intro.
              inversion H.
              tauto.
            tauto.
        * assert (ImplicationF p1_1 p1_2 <> BiconditionalF p2_1 p2_2).
            intro.
            inversion H.
          tauto.
      - intros p2.
        destruct p2.
        * assert (BiconditionalF p1_1 p1_2 <> AtomF i).
            intro.
            inversion H.
          tauto.
        * assert (BiconditionalF p1_1 p1_2 <> ContradictionF).
            intro.
            inversion H.
          tauto.
        * assert (BiconditionalF p1_1 p1_2 <> NegationF p2).
            intro.
            inversion H.
          tauto.
        * assert (BiconditionalF p1_1 p1_2 <> ConjunctionF p2_1 p2_2).
            intro.
            inversion H.
          tauto.
        * assert (BiconditionalF p1_1 p1_2 <> DisjunctionF p2_1 p2_2).
            intro.
            inversion H.
          tauto.
        * assert (BiconditionalF p1_1 p1_2 <> ImplicationF p2_1 p2_2).
            intro.
            inversion H.
          tauto.
        * destruct (IHp1_1 p2_1).
            destruct (IHp1_2 p2_2).
              subst.
              intuition.
              assert (BiconditionalF p1_1 p1_2 <> BiconditionalF p2_1 p2_2).
                intro.
                inversion H.
                tauto.
              tauto.
            assert (BiconditionalF p1_1 p1_2 <> BiconditionalF p2_1 p2_2).
              intro.
              inversion H.
              tauto.
            tauto.
    Qed.

    Fixpoint rankOfFormula (p : Formula) : nat :=
      match p with
      | AtomF i => 0
      | ContradictionF => 1
      | NegationF p1 => S (rankOfFormula p1)
      | ConjunctionF p1 p2 => S (max (rankOfFormula p1) (rankOfFormula p2))
      | DisjunctionF p1 p2 => S (max (rankOfFormula p1) (rankOfFormula p2))
      | ImplicationF p1 p2 => S (max (rankOfFormula p1) (rankOfFormula p2))
      | BiconditionalF p1 p2 => S (max (rankOfFormula p1) (rankOfFormula p2))
      end
    .

    Fixpoint enum_formula_aux (rank : nat) (seed0 : nat) : Formula :=
      match rank with
      | 0 =>
        let i := seed0 in
        AtomF i
      | S rank' =>
        let (seed1, piece1) := mapsLineToPlane seed0 in
        match piece1 with
        | 0 => ContradictionF
        | S 0 => NegationF (enum_formula_aux rank' seed1) 
        | S (S 0) =>
          let (seed2, seed3) := mapsLineToPlane seed1 in
          ConjunctionF (enum_formula_aux rank' seed2) (enum_formula_aux rank' seed3)
        | S (S (S 0)) =>
          let (seed2, seed3) := mapsLineToPlane seed1 in
          DisjunctionF (enum_formula_aux rank' seed2) (enum_formula_aux rank' seed3)
        | S (S (S (S 0))) =>
          let (seed2, seed3) := mapsLineToPlane seed1 in
          ImplicationF (enum_formula_aux rank' seed2) (enum_formula_aux rank' seed3)
        | S (S (S (S (S 0)))) =>
          let (seed2, seed3) := mapsLineToPlane seed1 in
          BiconditionalF (enum_formula_aux rank' seed2) (enum_formula_aux rank' seed3)
        | S (S (S (S (S (S i))))) => AtomF i
        end
      end
    .

    Lemma enum_formula_aux_property :
      forall p : Formula,
      forall rank : nat,
      rankOfFormula p <= rank ->
      exists seed : nat,
      enum_formula_aux rank seed = p.
    Proof.
      assert (
        forall x : nat,
        forall y : nat,
        forall z : nat,
        (y, z) = mapsLineToPlane x <-> x = sum_from_0_to (y + z) + z
      ).
        intros x y z.
        constructor.
        intro.
        apply mapsLineToPlane_is_injective.
        intuition.
        intro.
        subst.
        apply mapsLineToPlane_is_surjective.
      intros p.
      induction p.
      - intros r.
        simpl.
        intro.
        destruct r.
        * exists i.
          simpl.
          tauto.
        * assert (exists seed : nat, (0, S (S (S (S (S (S i)))))) = mapsLineToPlane seed).
          exists (sum_from_0_to (0 + S (S (S (S (S (S i)))))) + S (S (S (S (S (S i)))))).
          apply (proj2 (H (sum_from_0_to (0 + S (S (S (S (S (S i)))))) + S (S (S (S (S (S i)))))) 0 (S (S (S (S (S (S i))))))) eq_refl).
          destruct H1 as [seed H1].
          exists seed.
          simpl.
          rewrite <- H1.
          tauto.
      - intros r.
        simpl.
        intro.
        inversion H0.
          exists 0.
          simpl.
          tauto.
          exists 0.
          simpl.
          tauto.
      - intros r.
        simpl.
        intro.
        assert (exists rank : nat, r = S rank).
          inversion H0.
          exists (rankOfFormula p).
          tauto.
          exists m.
          tauto.
        destruct H1 as [rank H1].
        rewrite H1 in H0.
        assert (rankOfFormula p <= rank).
          lia.
        subst.
        destruct (IHp rank H2) as [seed H1].
        exists (sum_from_0_to (seed + 1) + 1).
        assert ((seed, 1) = mapsLineToPlane (sum_from_0_to (seed + 1) + 1)).
          apply (H ((sum_from_0_to (seed + 1) + 1)) seed 1).
          intuition.
        simpl in *.
        rewrite <- H3.
        rewrite H1.
        tauto.
      - intros r.
        simpl.
        intro.
        assert (exists rank : nat, r = S rank).
          inversion H0.
          exists (Init.Nat.max (rankOfFormula p1) (rankOfFormula p2)).
          tauto.
          exists m.
          tauto.
        destruct H1 as [rank H1].
        rewrite H1 in H0.
        assert ((Init.Nat.max (rankOfFormula p1) (rankOfFormula p2)) <= rank).
          lia.
        subst.
        destruct (IHp1 rank) as [seed2 H3].
          lia.
        destruct (IHp2 rank) as [seed3 H4].
          lia.
        assert (exists seed : nat, (sum_from_0_to (seed2 + seed3) + seed3, 2) = mapsLineToPlane seed).
          exists (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + 2) + 2).
            apply (proj2 (H (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + 2) + 2) (sum_from_0_to (seed2 + seed3) + seed3) 2)).
            tauto.
        destruct H1 as [seed H1].
        exists (seed).
        simpl.
        rewrite <- H1.
        assert ((seed2, seed3) = mapsLineToPlane (sum_from_0_to (seed2 + seed3) + seed3)).
          apply (proj2 (H (sum_from_0_to (seed2 + seed3) + seed3) seed2 seed3)).
          tauto.
        rewrite <- H5.
        rewrite H3.
        rewrite H4.
        tauto.
      - intros r.
        simpl.
        intro.
        assert (exists rank : nat, r = S rank).
          inversion H0.
          exists (Init.Nat.max (rankOfFormula p1) (rankOfFormula p2)).
          tauto.
          exists m.
          tauto.
        destruct H1 as [rank H1].
        rewrite H1 in H0.
        assert ((Init.Nat.max (rankOfFormula p1) (rankOfFormula p2)) <= rank).
          lia.
        subst.
        destruct (IHp1 rank) as [seed2 H3].
          lia.
        destruct (IHp2 rank) as [seed3 H4].
          lia.
        assert (exists seed : nat, (sum_from_0_to (seed2 + seed3) + seed3, 3) = mapsLineToPlane seed).
          exists (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + 3) + 3).
            apply (proj2 (H (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + 3) + 3) (sum_from_0_to (seed2 + seed3) + seed3) 3)).
            tauto.
        destruct H1 as [seed H1].
        exists (seed).
        simpl.
        rewrite <- H1.
        assert ((seed2, seed3) = mapsLineToPlane (sum_from_0_to (seed2 + seed3) + seed3)).
          apply (proj2 (H (sum_from_0_to (seed2 + seed3) + seed3) seed2 seed3)).
          tauto.
        rewrite <- H5.
        rewrite H3.
        rewrite H4.
        tauto.
      - intros r.
        simpl.
        intro.
        assert (exists rank : nat, r = S rank).
          inversion H0.
          exists (Init.Nat.max (rankOfFormula p1) (rankOfFormula p2)).
          tauto.
          exists m.
          tauto.
        destruct H1 as [rank H1].
        rewrite H1 in H0.
        assert ((Init.Nat.max (rankOfFormula p1) (rankOfFormula p2)) <= rank).
          lia.
        subst.
        destruct (IHp1 rank) as [seed2 H3].
          lia.
        destruct (IHp2 rank) as [seed3 H4].
          lia.
        assert (exists seed : nat, (sum_from_0_to (seed2 + seed3) + seed3, 4) = mapsLineToPlane seed).
          exists (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + 4) + 4).
            apply (proj2 (H (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + 4) + 4) (sum_from_0_to (seed2 + seed3) + seed3) 4)).
            tauto.
        destruct H1 as [seed H1].
        exists (seed).
        simpl.
        rewrite <- H1.
        assert ((seed2, seed3) = mapsLineToPlane (sum_from_0_to (seed2 + seed3) + seed3)).
          apply (proj2 (H (sum_from_0_to (seed2 + seed3) + seed3) seed2 seed3)).
          tauto.
        rewrite <- H5.
        rewrite H3.
        rewrite H4.
        tauto.
      - intros r.
        simpl.
        intro.
        assert (exists rank : nat, r = S rank).
          inversion H0.
          exists (Init.Nat.max (rankOfFormula p1) (rankOfFormula p2)).
          tauto.
          exists m.
          tauto.
        destruct H1 as [rank H1].
        rewrite H1 in H0.
        assert ((Init.Nat.max (rankOfFormula p1) (rankOfFormula p2)) <= rank).
          lia.
        subst.
        destruct (IHp1 rank) as [seed2 H3].
          lia.
        destruct (IHp2 rank) as [seed3 H4].
          lia.
        assert (exists seed : nat, (sum_from_0_to (seed2 + seed3) + seed3, 5) = mapsLineToPlane seed).
          exists (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + 5) + 5).
            apply (proj2 (H (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + 5) + 5) (sum_from_0_to (seed2 + seed3) + seed3) 5)).
            tauto.
        destruct H1 as [seed H1].
        exists (seed).
        simpl.
        rewrite <- H1.
        assert ((seed2, seed3) = mapsLineToPlane (sum_from_0_to (seed2 + seed3) + seed3)).
          apply (proj2 (H (sum_from_0_to (seed2 + seed3) + seed3) seed2 seed3)).
          tauto.
        rewrite <- H5.
        rewrite H3.
        rewrite H4.
        tauto.
    Qed.

    Definition enumerateFormula (n : nat) : Formula :=
      let (x, y) := mapsLineToPlane n in
      enum_formula_aux x y
    .

    Theorem Formula_is_enumerable : 
      forall p : Formula,
      exists n : nat, enumerateFormula n = p.
    Proof.
      intros p.
      assert (exists seed : nat, enum_formula_aux (rankOfFormula p) seed = p).
        apply (enum_formula_aux_property p (rankOfFormula p)).
        lia.
      destruct H as [seed H].
      exists (sum_from_0_to (rankOfFormula p + seed) + seed).
      assert ((rankOfFormula p, seed) = mapsLineToPlane (sum_from_0_to (rankOfFormula p + seed) + seed)).
        apply mapsLineToPlane_is_surjective.
      unfold enumerateFormula.
      rewrite <- H0.
      apply H.
    Qed.

  End Syntax.

  Section Semantics.

    Definition satisfies (structure : Formula -> Prop) (p : Formula) : Prop :=
      structure p
    .

    Definition preservesContradiction (structure : Formula -> Prop) : Prop :=
      satisfies structure ContradictionF <-> (False)
    .

    Definition preservesNegation (structure : Formula -> Prop) : Prop :=
      forall p1 : Formula, satisfies structure (NegationF p1) <-> (~ satisfies structure p1)
    .

    Definition preservesConjunction (structure : Formula -> Prop) : Prop :=
      forall p1 : Formula, forall p2 : Formula, satisfies structure (ConjunctionF p1 p2) <-> (satisfies structure p1 /\ satisfies structure p2)
    .

    Definition preservesDisjunction (structure : Formula -> Prop) : Prop :=
      forall p1 : Formula, forall p2 : Formula, satisfies structure (DisjunctionF p1 p2) <-> (satisfies structure p1 \/ satisfies structure p2)
    .

    Definition preservesImplication (structure : Formula -> Prop) : Prop :=
      forall p1 : Formula, forall p2 : Formula, satisfies structure (ImplicationF p1 p2) <-> (satisfies structure p1 -> satisfies structure p2)
    .

    Definition preservesBiconditional (structure : Formula -> Prop) : Prop :=
      forall p1 : Formula, forall p2 : Formula, satisfies structure (BiconditionalF p1 p2) <-> (satisfies structure p1 <-> satisfies structure p2)
    .

    Definition isStructure (structure : Formula -> Prop) : Prop :=
      preservesContradiction structure /\ preservesNegation structure /\ preservesConjunction structure /\ preservesDisjunction structure /\ preservesImplication structure /\ preservesBiconditional structure /\ (forall p1 : Formula, satisfies structure (NegationF (NegationF p1)) -> satisfies structure p1)
    .

    Definition Entails (hs : Ensemble Formula) (c : Formula) : Prop :=
      forall structure : Formula -> Prop, isStructure structure -> (forall h : Formula, member h hs -> satisfies structure h) -> satisfies structure c 
    .

    Lemma extendEntails :
      forall hs1 : Ensemble Formula,
      forall c : Formula,
      Entails hs1 c ->
      forall hs2 : Ensemble Formula,
      isSubsetOf hs1 hs2 ->
      Entails hs2 c.
    Proof.
      intros hs1 c.
      intro.
      intros hs2.
      intro.
      intros structure.
      intro.
      intro.
      apply H.
      apply H1.
      intros h.
      intro.
      apply H2.
      apply H0.
      apply H3.
    Qed.

  End Semantics.

  Section InferenceRules.

    Inductive Infers : Ensemble Formula -> Formula -> Prop :=
    | ByAssumption :
      forall hs : Ensemble Formula,
      forall h : Formula,
      member h hs ->
      Infers hs h
    | ContradictionI :
      forall hs : Ensemble Formula,
      forall a : Formula,
      Infers hs a ->
      Infers hs (NegationF a) ->
      Infers hs ContradictionF
    | ContradictionE :
      forall hs : Ensemble Formula,
      forall a : Formula,
      Infers hs ContradictionF ->
      Infers hs a
    | NegationI :
      forall hs : Ensemble Formula,
      forall a : Formula,
      Infers (insert a hs) ContradictionF ->
      Infers hs (NegationF a)
    | NegationE :
      forall hs : Ensemble Formula,
      forall a : Formula,
      Infers (insert (NegationF a) hs) ContradictionF ->
      Infers hs a
    | ConjunctionI :
      forall hs : Ensemble Formula,
      forall a : Formula,
      forall b : Formula,
      Infers hs a ->
      Infers hs b ->
      Infers hs (ConjunctionF a b)
    | ConjunctionE1 :
      forall hs : Ensemble Formula,
      forall a : Formula,
      forall b : Formula,
      Infers hs (ConjunctionF a b) ->
      Infers hs a
    | ConjunctionE2 :
      forall hs : Ensemble Formula,
      forall a : Formula,
      forall b : Formula,
      Infers hs (ConjunctionF a b) ->
      Infers hs b
    | DisjunctionI1 :
      forall hs : Ensemble Formula,
      forall a : Formula,
      forall b : Formula,
      Infers hs a ->
      Infers hs (DisjunctionF a b)
    | DisjunctionI2 :
      forall hs : Ensemble Formula,
      forall a : Formula,
      forall b : Formula,
      Infers hs b ->
      Infers hs (DisjunctionF a b)
    | DisjunctionE :
      forall hs : Ensemble Formula,
      forall a : Formula,
      forall b : Formula,
      forall c : Formula,
      Infers hs (DisjunctionF a b) ->
      Infers (insert a hs) c ->
      Infers (insert b hs) c ->
      Infers hs c
    | ImplicationI :
      forall hs : Ensemble Formula,
      forall a : Formula,
      forall b : Formula,
      Infers (insert a hs) b ->
      Infers hs (ImplicationF a b)
    | ImplicationE :
      forall hs : Ensemble Formula,
      forall a : Formula,
      forall b : Formula,
      Infers hs (ImplicationF a b) ->
      Infers hs a ->
      Infers hs b
    | BiconditionalI :
      forall hs : Ensemble Formula,
      forall a : Formula,
      forall b : Formula,
      Infers (insert a hs) b ->
      Infers (insert b hs) a ->
      Infers hs (BiconditionalF a b)
    | BiconditionalE1 :
      forall hs : Ensemble Formula,
      forall a : Formula,
      forall b : Formula,
      Infers hs (BiconditionalF a b) ->
      Infers hs a ->
      Infers hs b
    | BiconditionalE2 :
      forall hs : Ensemble Formula,
      forall a : Formula,
      forall b : Formula,
      Infers hs (BiconditionalF a b) ->
      Infers hs b ->
      Infers hs a
    .

    Example ExclusiveMiddle :
      forall p : Formula,
      Infers empty (DisjunctionF p (NegationF p)).
    Proof.
      intros p.
      apply (NegationE empty (DisjunctionF p (NegationF p))).
      apply (ContradictionI (insert (NegationF (DisjunctionF p (NegationF p))) empty) (DisjunctionF p (NegationF p))).
      apply (DisjunctionI2 (insert (NegationF (DisjunctionF p (NegationF p))) empty) p (NegationF p)).
      apply (NegationI (insert (NegationF (DisjunctionF p (NegationF p))) empty) p).
      apply (ContradictionI (insert p (insert (NegationF (DisjunctionF p (NegationF p))) empty)) (DisjunctionF p (NegationF p))).
      apply (DisjunctionI1 (insert p (insert (NegationF (DisjunctionF p (NegationF p))) empty)) p (NegationF p)).
      apply (ByAssumption (insert p (insert (NegationF (DisjunctionF p (NegationF p))) empty)) p).
      apply UnionR.
      apply Singleton.
      apply (ByAssumption (insert p (insert (NegationF (DisjunctionF p (NegationF p))) empty)) (NegationF (DisjunctionF p (NegationF p)))).
      apply UnionL.
      apply UnionR.
      apply Singleton.
      apply (ByAssumption (insert (NegationF (DisjunctionF p (NegationF p))) empty) (NegationF (DisjunctionF p (NegationF p)))).
      apply UnionR.
      apply Singleton.
    Qed.

    Lemma cut_property :
      forall hs : Ensemble Formula,
      forall p1 : Formula,
      forall p2 : Formula,
      Infers hs p1 ->
      Infers (insert p1 hs) p2 ->
      Infers hs p2.
    Proof.
      intros hs p1 p2.
      intro.
      intro.
      assert (Infers hs (ImplicationF p1 p2)).
        apply (ImplicationI hs p1 p2 H0).
      apply (ImplicationE hs p1 p2 H1 H).
    Qed.

  End InferenceRules.

  Section Soundness.

    Lemma extendInfers :
      forall hs1 : Ensemble Formula,
      forall c : Formula,
      Infers hs1 c ->
      forall hs2 : Ensemble Formula,
      isSubsetOf hs1 hs2 ->
      Infers hs2 c.
    Proof.
      intros hs1 c.
      intro.
      induction H.
      - intros hs2.
        intro.
        apply (ByAssumption hs2 h).
        apply (H0 h H).
      - intros hs2.
        intro.
        apply (ContradictionI hs2 a).
        apply (IHInfers1 hs2 H1).
        apply (IHInfers2 hs2 H1).
      - intros hs2.
        intro.
        apply (ContradictionE hs2 a).
        apply (IHInfers hs2 H0).
      - intros hs2.
        intro.
        apply (NegationI hs2 a).
        apply (IHInfers (insert a hs2)).
        apply isSubsetOf_insert.
        apply H0.
      - intros hs2.
        intro.
        apply (NegationE hs2 a).
        apply (IHInfers (insert (NegationF a) hs2)).
        apply isSubsetOf_insert.
        apply H0.
      - intros hs2.
        intro.
        apply (ConjunctionI hs2 a b).
        apply (IHInfers1 hs2 H1).
        apply (IHInfers2 hs2 H1).
      - intros hs2.
        intro.
        apply (ConjunctionE1 hs2 a b).
        apply (IHInfers hs2 H0).
      - intros hs2.
        intro.
        apply (ConjunctionE2 hs2 a b).
        apply (IHInfers hs2 H0).
      - intros hs2.
        intro.
        apply (DisjunctionI1 hs2 a b).
        apply (IHInfers hs2 H0).
      - intros hs2.
        intro.
        apply (DisjunctionI2 hs2 a b).
        apply (IHInfers hs2 H0).
      - intros hs2.
        intro.
        apply (DisjunctionE hs2 a b c).
        apply (IHInfers1 hs2 H2).
        apply (IHInfers2 (insert a hs2)).
        apply isSubsetOf_insert.
        apply H2.
        apply (IHInfers3 (insert b hs2)).
        apply isSubsetOf_insert.
        apply H2.
      - intros hs2.
        intro.
        apply (ImplicationI hs2 a b).
        apply (IHInfers (insert a hs2)).
        apply isSubsetOf_insert.
        apply H0.
      - intros hs2.
        intro.
        apply (ImplicationE hs2 a b).
        apply (IHInfers1 hs2 H1).
        apply (IHInfers2 hs2 H1).
      - intros hs2.
        intro.
        apply (BiconditionalI hs2 a b).
        apply (IHInfers1 (insert a hs2)).
        apply isSubsetOf_insert.
        apply H1.
        apply (IHInfers2 (insert b hs2)).
        apply isSubsetOf_insert.
        apply H1.
      - intros hs2.
        intro.
        apply (BiconditionalE1 hs2 a b).
        apply (IHInfers1 hs2 H1).
        apply (IHInfers2 hs2 H1).
      - intros hs2.
        intro.
        apply (BiconditionalE2 hs2 a b).
        apply (IHInfers1 hs2 H1).
        apply (IHInfers2 hs2 H1).
    Qed.

    Lemma ByAssumption_preserves :
      forall hs : Ensemble Formula,
      forall a : Formula,
      member a hs ->
      Entails hs a.
    Proof.
      intros hs c H.
      apply (extendEntails (singleton c) c).
      intros v.
      intros.
      apply H1.
      apply Singleton.
      intros h.
      intro.
      inversion H0.
      subst.
      apply H.
    Qed.

    Lemma ContradictionI_preserves :
      forall hs : Ensemble Formula,
      forall a : Formula,
      Entails hs a ->
      Entails hs (NegationF a) ->
      Entails hs ContradictionF.
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesNegation v).
        unfold isStructure in H1.
        intuition.
      assert (satisfies v a).
        apply (H v H1 H2).
      assert (satisfies v (NegationF a)).
        apply (H0 v H1 H2).
      contradiction (proj1 (H3 a)).
    Qed.

    Lemma ContradictionE_preserves :
      forall hs : Ensemble Formula,
      forall a : Formula,
      Entails hs ContradictionF ->
      Entails hs a.
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesContradiction v).
        unfold isStructure in H0.
        intuition.
      assert (satisfies v ContradictionF).
        apply (H v H0 H1).
      contradiction (proj1 H2).
    Qed.

    Lemma NegationI_preserves :
      forall hs : Ensemble Formula,
      forall a : Formula,
      Entails (insert a hs) ContradictionF ->
      Entails hs (NegationF a).
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesNegation v).
        unfold isStructure in H0.
        intuition.
      assert (preservesContradiction v).
        unfold isStructure in H0.
        intuition.
      apply (proj2 (H2 a)).
      intro.
      assert (satisfies v ContradictionF).
        apply (H v).
        apply H0.
        intros h.
        intro.
        inversion H5.
        subst.
        apply (H1 h H6).
        subst.
        inversion H6.
        subst.
        apply H4.
      contradiction (proj1 H3).
    Qed.

    Lemma NegationE_preserves :
      forall hs : Ensemble Formula,
      forall a : Formula,
      Entails (insert (NegationF a) hs) ContradictionF ->
      Entails hs a.
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesNegation v).
        unfold isStructure in H0.
        intuition.
      assert (preservesContradiction v).
        unfold isStructure in H0.
        intuition.
      assert (forall p1 : Formula, satisfies v (NegationF (NegationF p1)) -> satisfies v p1).
        unfold isStructure in H0.
        intuition.
      apply (H4 a).
      apply (NegationI_preserves hs (NegationF a)).
      apply H.
      apply H0.
      apply H1.
    Qed.

    Lemma ConjunctionI_preserves :
      forall hs : Ensemble Formula,
      forall a b : Formula,
      Entails hs a ->
      Entails hs b ->
      Entails hs (ConjunctionF a b).
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesConjunction v).
        unfold isStructure in H1.
        intuition.
      apply (proj2 (H3 a b)).
      constructor.
      apply H.
      apply H1.
      apply H2.
      apply H0.
      apply H1.
      apply H2.
    Qed.

    Lemma ConjunctionE1_preserves :
      forall hs : Ensemble Formula,
      forall a b : Formula,
      Entails hs (ConjunctionF a b) ->
      Entails hs a.
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesConjunction v).
        unfold isStructure in H0.
        intuition.
      destruct (proj1 (H2 a b)).
        apply H.
        apply H0.
        apply H1.
      apply H3.
    Qed.

    Lemma ConjunctionE2_preserves :
      forall hs : Ensemble Formula,
      forall a b : Formula,
      Entails hs (ConjunctionF a b) ->
      Entails hs b.
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesConjunction v).
        unfold isStructure in H0.
        intuition.
      destruct (proj1 (H2 a b)).
        apply H.
        apply H0.
        apply H1.
      apply H4.
    Qed.

    Lemma DisjunctionI1_preserves :
      forall hs : Ensemble Formula,
      forall a b : Formula,
      Entails hs a ->
      Entails hs (DisjunctionF a b).
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesDisjunction v).
        unfold isStructure in H0.
        intuition.
      apply (proj2 (H2 a b)).
      apply or_introl.
      apply H.
      apply H0.
      apply H1.
    Qed.

    Lemma DisjunctionI2_preserves :
      forall hs : Ensemble Formula,
      forall a b : Formula,
      Entails hs b ->
      Entails hs (DisjunctionF a b).
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesDisjunction v).
        unfold isStructure in H0.
        intuition.
      apply (proj2 (H2 a b)).
      apply or_intror.
      apply H.
      apply H0.
      apply H1.
    Qed.

    Lemma DisjunctionE_preserves :
      forall hs : Ensemble Formula,
      forall a b c : Formula,
      Entails hs (DisjunctionF a b) ->
      Entails (insert a hs) c ->
      Entails (insert b hs) c ->
      Entails hs c.
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesDisjunction v).
        unfold isStructure in H2.
        intuition.
      assert (satisfies v a \/ satisfies v b).
        apply (proj1 (H4 a b)).
        apply H.
        apply H2.
        apply H3.
      destruct H5.
      apply H0.
      apply H2.
      intros h.
      intro.
      inversion H6.
      subst.
      apply H3.
      apply H7.
      subst.
      inversion H7.
      subst.
      apply H5.
      apply H1.
      apply H2.
      intros h.
      intro.
      inversion H6.
      subst.
      apply H3.
      apply H7.
      subst.
      inversion H7.
      subst.
      apply H5.
    Qed.

    Lemma ImplicationI_preserves :
      forall hs : Ensemble Formula,
      forall a b : Formula,
      Entails (insert a hs) b ->
      Entails hs (ImplicationF a b).
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesImplication v).
        unfold isStructure in H0.
        intuition.
      apply (proj2 (H2 a b)).
      intro.
      apply H.
      apply H0.
      intros h.
      intro.
      inversion H4.
      subst.
      apply (H1 h).
      apply H5.
      inversion H5.
      subst.
      apply H3.
    Qed.

    Lemma ImplicationE_preserves :
      forall hs : Ensemble Formula,
      forall a b : Formula,
      Entails hs (ImplicationF a b) ->
      Entails hs a ->
      Entails hs b.
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesImplication v).
        unfold isStructure in H1.
        intuition.
      apply (proj1 (H3 a b)).
      apply H.
      apply H1.
      apply H2.
      apply H0.
      apply H1.
      apply H2.
    Qed.

    Lemma BiconditionalI_preserves :
      forall hs : Ensemble Formula,
      forall a b : Formula,
      Entails (insert a hs) b ->
      Entails (insert b hs) a ->
      Entails hs (BiconditionalF a b).
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesBiconditional v).
        unfold isStructure in H1.
        intuition.
      apply (proj2 (H3 a b)).
      constructor.
      intro.
      apply H.
      apply H1.
      intros h.
      intro.
      inversion H5.
      subst.
      apply (H2 h).
      apply H6.
      inversion H6.
      subst.
      apply H4.
      intro.
      apply H0.
      apply H1.
      intros h.
      intro.
      inversion H5.
      subst.
      apply (H2 h).
      apply H6.
      inversion H6.
      subst.
      apply H4.
    Qed.

    Lemma BiconditionalE1_preserves :
      forall hs : Ensemble Formula,
      forall a b : Formula,
      Entails hs (BiconditionalF a b) ->
      Entails hs a ->
      Entails hs b.
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesBiconditional v).
        unfold isStructure in H1.
        intuition.
      apply (proj1 (H3 a b)).
      apply H.
      apply H1.
      apply H2.
      apply H0.
      apply H1.
      apply H2.
    Qed.

    Lemma BiconditionalE2_preserves :
      forall hs : Ensemble Formula,
      forall a b : Formula,
      Entails hs (BiconditionalF a b) ->
      Entails hs b ->
      Entails hs a.
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesBiconditional v).
        unfold isStructure in H1.
        intuition.
      apply (proj1 (H3 a b)).
      apply H.
      apply H1.
      apply H2.
      apply H0.
      apply H1.
      apply H2.
    Qed.

    Theorem Soundness :
      forall hs : Ensemble Formula,
      forall c : Formula,
      Infers hs c ->
      Entails hs c.
    Proof.
      intros hs c H.
      induction H.
      - apply (ByAssumption_preserves hs h H).
      - apply (ContradictionI_preserves hs a IHInfers1 IHInfers2).
      - apply (ContradictionE_preserves hs a IHInfers).
      - apply (NegationI_preserves hs a IHInfers).
      - apply (NegationE_preserves hs a IHInfers).
      - apply (ConjunctionI_preserves hs a b IHInfers1 IHInfers2).
      - apply (ConjunctionE1_preserves hs a b IHInfers).
      - apply (ConjunctionE2_preserves hs a b IHInfers).
      - apply (DisjunctionI1_preserves hs a b IHInfers).
      - apply (DisjunctionI2_preserves hs a b IHInfers).
      - apply (DisjunctionE_preserves hs a b c IHInfers1 IHInfers2 IHInfers3).
      - apply (ImplicationI_preserves hs a b IHInfers).
      - apply (ImplicationE_preserves hs a b IHInfers1 IHInfers2).
      - apply (BiconditionalI_preserves hs a b IHInfers1 IHInfers2).
      - apply (BiconditionalE1_preserves hs a b IHInfers1 IHInfers2).
      - apply (BiconditionalE2_preserves hs a b IHInfers1 IHInfers2).
    Qed.

  End Soundness.

  Section LindenbaumBooleanAlgebra.

    Program Instance LindenbaumBooleanAlgebra : CountableBooleanAlgebra Formula :=
      { eqB := fun p1 : Formula => fun p2 : Formula => Infers (singleton p1) p2 /\ Infers (singleton p2) p1
      ; trueB := ImplicationF ContradictionF ContradictionF
      ; falseB := ContradictionF
      ; negB := NegationF
      ; andB := ConjunctionF
      ; orB := DisjunctionF
      ; enumB := enumerateFormula
      }
    .

    Next Obligation.
      assert (Infers (singleton b1) b1).
        apply ByAssumption.
        apply Singleton.
      tauto.
    Defined.

    Next Obligation.
      constructor.
      apply (cut_property (singleton b1) b2 b3).
      apply H.
      apply (extendInfers (singleton b2) b3 H0).
      intros p.
      intro.
      apply UnionR.
      apply H3.
      apply (cut_property (singleton b3) b2 b1).
      apply H1.
      apply (extendInfers (singleton b2) b1 H2).
      intros p.
      intro.
      apply UnionR.
      apply H3.
    Defined.

    Next Obligation.
      assert (Infers (singleton (ImplicationF ContradictionF ContradictionF)) (ImplicationF ContradictionF ContradictionF)).
        apply ByAssumption.
        apply Singleton.
      tauto.
    Defined.

    Next Obligation.
      assert (Infers (singleton ContradictionF) ContradictionF).
        apply ByAssumption.
        apply Singleton.
      tauto.
    Defined.

    Next Obligation.
      constructor.
      apply NegationI.
      apply (ContradictionI (insert b1' (singleton (NegationF b1))) b1).
      apply (extendInfers (singleton b1') b1 H0).
      intros p.
      intro.
      apply UnionR.
      apply H1.
      apply ByAssumption.
      apply UnionL.
      apply Singleton.
      apply NegationI.
      apply (ContradictionI (insert b1 (singleton (NegationF b1'))) b1').
      apply (extendInfers (singleton b1) b1' H).
      intros p.
      intro.
      apply UnionR.
      apply H1.
      apply ByAssumption.
      apply UnionL.
      apply Singleton.
    Defined.
    
    Next Obligation.
      constructor.
      apply ConjunctionI.
      apply (cut_property (singleton (ConjunctionF b1 b2)) b1 b1').
      apply (ConjunctionE1 (singleton (ConjunctionF b1 b2)) b1 b2).
      apply ByAssumption.
      apply Singleton.
      apply (extendInfers (singleton b1) b1' H).
      intros p.
      intro.
      apply UnionR.
      apply H3.
      apply (cut_property (singleton (ConjunctionF b1 b2)) b2 b2').
      apply (ConjunctionE2 (singleton (ConjunctionF b1 b2)) b1 b2).
      apply ByAssumption.
      apply Singleton.
      apply (extendInfers (singleton b2) b2' H0).
      intros p.
      intro.
      apply UnionR.
      apply H3.
      apply ConjunctionI.
      apply (cut_property (singleton (ConjunctionF b1' b2')) b1' b1).
      apply (ConjunctionE1 (singleton (ConjunctionF b1' b2')) b1' b2').
      apply ByAssumption.
      apply Singleton.
      apply (extendInfers (singleton b1') b1 H2).
      intros p.
      intro.
      apply UnionR.
      apply H3.
      apply (cut_property (singleton (ConjunctionF b1' b2')) b2' b2).
      apply (ConjunctionE2 (singleton (ConjunctionF b1' b2')) b1' b2').
      apply ByAssumption.
      apply Singleton.
      apply (extendInfers (singleton b2') b2 H1).
      intros p.
      intro.
      apply UnionR.
      apply H3.
    Defined.

    Next Obligation.
      constructor.
      apply (DisjunctionE (singleton (DisjunctionF b1 b2)) b1 b2 (DisjunctionF b1' b2')).
      apply ByAssumption.
      apply Singleton.
      apply (DisjunctionI1 (insert b1 (singleton (DisjunctionF b1 b2))) b1' b2').
      apply (extendInfers (singleton b1) b1' H).
      intros p.
      intro.
      apply UnionR.
      apply H3.
      apply (DisjunctionI2 (insert b2 (singleton (DisjunctionF b1 b2))) b1' b2').
      apply (extendInfers (singleton b2) b2' H0).
      intros p.
      intro.
      apply UnionR.
      apply H3.
      apply (DisjunctionE (singleton (DisjunctionF b1' b2')) b1' b2' (DisjunctionF b1 b2)).
      apply ByAssumption.
      apply Singleton.
      apply (DisjunctionI1 (insert b1' (singleton (DisjunctionF b1' b2'))) b1 b2).
      apply (extendInfers (singleton b1') b1 H2).
      intros p.
      intro.
      apply UnionR.
      apply H3.
      apply (DisjunctionI2 (insert b2' (singleton (DisjunctionF b1' b2'))) b1 b2).
      apply (extendInfers (singleton b2') b2 H1).
      intros p.
      intro.
      apply UnionR.
      apply H3.
    Defined.

    Next Obligation.
      constructor.
      apply ConjunctionI.
      apply ConjunctionI.
      apply (ConjunctionE1 (singleton (ConjunctionF b1 (ConjunctionF b2 b3))) b1 (ConjunctionF b2 b3)).
      apply ByAssumption.
      apply Singleton.
      apply (ConjunctionE1 (singleton (ConjunctionF b1 (ConjunctionF b2 b3))) b2 b3).
      apply (ConjunctionE2 (singleton (ConjunctionF b1 (ConjunctionF b2 b3))) b1 (ConjunctionF b2 b3)).
      apply ByAssumption.
      apply Singleton.
      apply (ConjunctionE2 (singleton (ConjunctionF b1 (ConjunctionF b2 b3))) b2 b3).
      apply (ConjunctionE2 (singleton (ConjunctionF b1 (ConjunctionF b2 b3))) b1 (ConjunctionF b2 b3)).
      apply ByAssumption.
      apply Singleton.
      apply ConjunctionI.
      apply (ConjunctionE1 (singleton (ConjunctionF (ConjunctionF b1 b2) b3)) b1 b2).
      apply (ConjunctionE1 (singleton (ConjunctionF (ConjunctionF b1 b2) b3)) (ConjunctionF b1 b2) b3).
      apply ByAssumption.
      apply Singleton.
      apply ConjunctionI.
      apply (ConjunctionE2 (singleton (ConjunctionF (ConjunctionF b1 b2) b3)) b1 b2).
      apply (ConjunctionE1 (singleton (ConjunctionF (ConjunctionF b1 b2) b3)) (ConjunctionF b1 b2) b3).
      apply ByAssumption.
      apply Singleton.
      apply (ConjunctionE2 (singleton (ConjunctionF (ConjunctionF b1 b2) b3)) (ConjunctionF b1 b2) b3).
      apply ByAssumption.
      apply Singleton.
    Defined.

    Next Obligation.
      constructor.
      apply (DisjunctionE (singleton (DisjunctionF b1 (DisjunctionF b2 b3))) b1 (DisjunctionF b2 b3)).
      apply ByAssumption.
      apply Singleton.
      apply (DisjunctionI1 (insert b1 (singleton (DisjunctionF b1 (DisjunctionF b2 b3)))) (DisjunctionF b1 b2) b3).
      apply (DisjunctionI1 (insert b1 (singleton (DisjunctionF b1 (DisjunctionF b2 b3)))) b1 b2).
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply (DisjunctionE (insert (DisjunctionF b2 b3) (singleton (DisjunctionF b1 (DisjunctionF b2 b3)))) b2 b3).
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply (DisjunctionI1 (insert b2 (insert (DisjunctionF b2 b3) (singleton (DisjunctionF b1 (DisjunctionF b2 b3))))) (DisjunctionF b1 b2) b3).
      apply (DisjunctionI2 (insert b2 (insert (DisjunctionF b2 b3) (singleton (DisjunctionF b1 (DisjunctionF b2 b3))))) b1 b2).
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply (DisjunctionI2 (insert b3 (insert (DisjunctionF b2 b3) (singleton (DisjunctionF b1 (DisjunctionF b2 b3))))) (DisjunctionF b1 b2) b3).
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply (DisjunctionE (singleton (DisjunctionF (DisjunctionF b1 b2) b3)) (DisjunctionF b1 b2) b3).
      apply ByAssumption.
      apply Singleton.
      apply (DisjunctionE (insert (DisjunctionF b1 b2) (singleton (DisjunctionF (DisjunctionF b1 b2) b3))) b1 b2).
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply (DisjunctionI1 (insert b1 (insert (DisjunctionF b1 b2) (singleton (DisjunctionF (DisjunctionF b1 b2) b3)))) b1 (DisjunctionF b2 b3)).
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply (DisjunctionI2 (insert b2 (insert (DisjunctionF b1 b2) (singleton (DisjunctionF (DisjunctionF b1 b2) b3)))) b1 (DisjunctionF b2 b3)).
      apply (DisjunctionI1 (insert b2 (insert (DisjunctionF b1 b2) (singleton (DisjunctionF (DisjunctionF b1 b2) b3)))) b2 b3).
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply (DisjunctionI2 (insert b3 (singleton (DisjunctionF (DisjunctionF b1 b2) b3))) b1 (DisjunctionF b2 b3)).
      apply (DisjunctionI2 (insert b3 (singleton (DisjunctionF (DisjunctionF b1 b2) b3))) b2 b3).
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
    Defined.

    Next Obligation.
      constructor.
      apply (ConjunctionE1 (singleton (ConjunctionF b1 b1)) b1 b1).
      apply ByAssumption.
      apply Singleton.
      apply ConjunctionI.
      apply ByAssumption.
      apply Singleton.
      apply ByAssumption.
      apply Singleton.
    Defined.

    Next Obligation.
      constructor.
      apply (DisjunctionE (singleton (DisjunctionF b1 b1)) b1 b1 b1).
      apply ByAssumption.
      apply Singleton.
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply DisjunctionI1.
      apply ByAssumption.
      apply Singleton.
    Defined.

    Next Obligation.
      constructor.
      apply ConjunctionI.
      apply (ConjunctionE2 (singleton (ConjunctionF b1 b2)) b1 b2).
      apply ByAssumption.
      apply Singleton.
      apply (ConjunctionE1 (singleton (ConjunctionF b1 b2)) b1 b2).
      apply ByAssumption.
      apply Singleton.
      apply ConjunctionI.
      apply (ConjunctionE2 (singleton (ConjunctionF b2 b1)) b2 b1).
      apply ByAssumption.
      apply Singleton.
      apply (ConjunctionE1 (singleton (ConjunctionF b2 b1)) b2 b1).
      apply ByAssumption.
      apply Singleton.
    Defined.

    Next Obligation.
      constructor.
      apply (DisjunctionE (singleton (DisjunctionF b1 b2)) b1 b2).
      apply ByAssumption.
      apply Singleton.
      apply (DisjunctionI2 (insert b1 (singleton (DisjunctionF b1 b2))) b2 b1).
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply (DisjunctionI1 (insert b2 (singleton (DisjunctionF b1 b2))) b2 b1).
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply (DisjunctionE (singleton (DisjunctionF b2 b1)) b2 b1).
      apply ByAssumption.
      apply Singleton.
      apply (DisjunctionI2 (insert b2 (singleton (DisjunctionF b2 b1))) b1 b2).
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply (DisjunctionI1 (insert b1 (singleton (DisjunctionF b2 b1))) b1 b2).
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
    Defined.

    Next Obligation.
      constructor.
      apply (DisjunctionE (singleton (ConjunctionF b1 (DisjunctionF b2 b3))) b2 b3).
      apply (ConjunctionE2 (singleton (ConjunctionF b1 (DisjunctionF b2 b3))) b1 (DisjunctionF b2 b3)).
      apply ByAssumption.
      apply Singleton.
      apply DisjunctionI1.
      apply ConjunctionI.
      apply (ConjunctionE1 _ b1 (DisjunctionF b2 b3)).
      apply ByAssumption.
      apply UnionL.
      apply Singleton.
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply DisjunctionI2.
      apply ConjunctionI.
      apply (ConjunctionE1 _ b1 (DisjunctionF b2 b3)).
      apply ByAssumption.
      apply UnionL.
      apply Singleton.
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply (DisjunctionE _ (ConjunctionF b1 b2) (ConjunctionF b1 b3)).
      apply ByAssumption.
      apply Singleton.
      apply ConjunctionI.
      apply (ConjunctionE1 _ b1 b2).
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply DisjunctionI1.
      apply (ConjunctionE2 _ b1 b2).
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply ConjunctionI.
      apply (ConjunctionE1 _ b1 b3).
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply DisjunctionI2.
      apply (ConjunctionE2 _ b1 b3).
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
    Defined.

    Next Obligation.
      constructor.
      apply ConjunctionI.
      apply (DisjunctionE _ b1 (ConjunctionF b2 b3)).
      apply ByAssumption.
      apply Singleton.
      apply DisjunctionI1.
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply DisjunctionI2.
      apply (ConjunctionE1 _ b2 b3).
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply (DisjunctionE _ b1 (ConjunctionF b2 b3)).
      apply ByAssumption.
      apply Singleton.
      apply DisjunctionI1.
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply DisjunctionI2.
      apply (ConjunctionE2 _ b2 b3).
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply (DisjunctionE _ b1 b2).
      apply (ConjunctionE1 _ (DisjunctionF b1 b2) (DisjunctionF b1 b3)).
      apply ByAssumption.
      apply Singleton.
      apply DisjunctionI1.
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply (DisjunctionE _ b1 b3).
      apply (ConjunctionE2 _ (DisjunctionF b1 b2) (DisjunctionF b1 b3)).
      apply ByAssumption.
      apply UnionL.
      apply Singleton.
      apply DisjunctionI1.
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply DisjunctionI2.
      apply ConjunctionI.
      apply ByAssumption.
      apply UnionL.
      apply UnionR.
      apply Singleton.
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
    Defined.

    Next Obligation.
      constructor.
      apply (ConjunctionE1 _ b1 (DisjunctionF b1 b2)).
      apply ByAssumption.
      apply Singleton.
      apply ConjunctionI.
      apply ByAssumption.
      apply Singleton.
      apply DisjunctionI1.
      apply ByAssumption.
      apply Singleton.
    Defined.

    Next Obligation.
      constructor.
      apply (DisjunctionE _ b1 (ConjunctionF b1 b2)).
      apply ByAssumption.
      apply Singleton.
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply (ConjunctionE1 _ b1 b2).
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply DisjunctionI1.
      apply ByAssumption.
      apply Singleton.
    Defined.

    Next Obligation.
      constructor.
      apply (ConjunctionE2 _ b1 ContradictionF).
      apply ByAssumption.
      apply Singleton.
      apply ConjunctionI.
      apply ContradictionE.
      apply ByAssumption.
      apply Singleton.
      apply ByAssumption.
      apply Singleton.
    Defined.

    Next Obligation.
      constructor.
      apply ImplicationI.
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply DisjunctionI2.
      apply ByAssumption.
      apply Singleton.
    Defined.

    Next Obligation.
      constructor.
      apply (DisjunctionE _ b1 ContradictionF).
      apply ByAssumption.
      apply Singleton.
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply ContradictionE.
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply DisjunctionI1.
      apply ByAssumption.
      apply Singleton.
    Defined.

    Next Obligation.
      constructor.
      apply (ConjunctionE1 _ b1 (ImplicationF ContradictionF ContradictionF)).
      apply ByAssumption.
      apply Singleton.
      apply ConjunctionI.
      apply ByAssumption.
      apply Singleton.
      apply ImplicationI.
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
    Defined.

    Next Obligation.
      constructor.
      apply (ContradictionI _ b1).
      apply (ConjunctionE1 _ b1 (NegationF b1)).
      apply ByAssumption.
      apply Singleton.
      apply (ConjunctionE2 _ b1 (NegationF b1)).
      apply ByAssumption.
      apply Singleton.
      apply ContradictionE.
      apply ByAssumption.
      apply Singleton.
    Defined.

    Next Obligation.
      constructor.
      apply ImplicationI.
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply (extendInfers empty (DisjunctionF b1 (NegationF b1)) (ExclusiveMiddle b1)).
      intros p.
      intro.
      inversion H.
    Defined.

    Next Obligation.
      apply Formula_is_enumerable.
    Defined.

    Lemma leq_LBA :
      forall b1 : Formula,
      forall b2 : Formula,
      eqB (andB b1 b2) b1 <-> Infers (singleton b1) b2.
    Proof.
      intros b1 b2.
      constructor.
      intro.
      destruct H.
      apply (ConjunctionE2 _ b1 b2).
      apply H0.
      intro.
      constructor.
      apply (ConjunctionE1 _ b1 b2).
      apply ByAssumption.
      apply Singleton.
      apply ConjunctionI.
      apply ByAssumption.
      apply Singleton.
      apply H.
    Qed.

    Lemma andBs_LBA :
      forall ps : list Formula,
      forall hs : Ensemble Formula,
      (forall p : Formula, In p ps -> member p hs) ->
      forall c : Formula,
      Infers (singleton (fold_right andB trueB ps)) c <-> (exists hs' : Ensemble Formula, (forall h : Formula, In h ps <-> member h hs') /\ Infers hs' c).
    Proof.
      intros ps.
      induction ps.
      - intros hs.
        intro.
        intros c.
        constructor.
        intro.
        exists empty.
        constructor.
        intros p.
        constructor.
        intro.
        inversion H1.
        intro.
        inversion H1.
        apply (ConjunctionE2 _ (ImplicationF ContradictionF ContradictionF) c).
        apply (cut_property empty (ImplicationF ContradictionF ContradictionF) (ConjunctionF (ImplicationF ContradictionF ContradictionF) c)).
        apply ImplicationI.
        apply ByAssumption.
        apply UnionR.
        apply Singleton.
        apply ConjunctionI.
        apply ByAssumption.
        apply UnionR.
        apply Singleton.
        apply (extendInfers (singleton (fold_right andB trueB [])) c H0).
        intros p.
        intro.
        apply UnionR.
        apply H1.
        intro.
        destruct H0 as [hs'].
        destruct H0.
        assert (isSubsetOf hs' empty).
          intros p.
          intro.
          assert (In p []).
            apply H0.
          apply H2.
        inversion H3.
        assert (Infers empty c).
          apply (extendInfers hs' c H1).
          apply H2.
        apply (extendInfers empty c H3).
          intros p.
          intro.
          inversion H4.
      - intros hs.
        intro.
        intros c.
        constructor.
        intro.
        assert (forall p : Formula, In p ps -> member p hs).
          intros p.
          intro.
          apply H.
          simpl.
          tauto.
        assert (Infers (singleton (fold_right andB trueB ps)) (ImplicationF a c)).
          apply ImplicationI.
          apply (cut_property (insert a (singleton (fold_right andB trueB ps))) (fold_right andB trueB (a :: ps)) c).
          simpl.
          apply ConjunctionI.
          apply ByAssumption.
          apply UnionR.
          apply Singleton.
          apply ByAssumption.
          apply UnionL.
          apply Singleton.
          apply (extendInfers (singleton (fold_right andB trueB (a :: ps))) c H0).
          intros p.
          intro.
          apply UnionR.
          apply H2.
        assert (exists hs' : Ensemble Formula, (forall h : Formula, In h ps <-> member h hs') /\ Infers hs' (ImplicationF a c)).
          apply (proj1 (IHps hs H1 (ImplicationF a c)) H2).
        destruct H3 as [hs'].
        exists (insert a hs').
        destruct H3.
        constructor.
        intros p.
        constructor.
        intro.
        inversion H5.
        subst.
        apply UnionR.
        apply Singleton.
        apply UnionL.
        apply H3.
        apply H6.
        intro.
        inversion H5.
        subst.
        simpl.
        apply or_intror.
        apply H3.
        apply H6.
        subst.
        inversion H6.
        subst.
        simpl.
        tauto.
        apply (cut_property (insert a hs') (ImplicationF a c) c).
        apply (extendInfers hs' (ImplicationF a c) H4).
        intros p.
        intro.
        apply UnionL.
        apply H5.
        apply (ImplicationE _ a c).
        apply ByAssumption.
        apply UnionR.
        apply Singleton.
        apply ByAssumption.
        apply UnionL.
        apply UnionR.
        apply Singleton.
        intro.
        destruct (in_dec eq_Formula_dec a ps).
        * assert (forall p : Formula, In p ps -> member p hs).
            intros p.
            intro.
            apply H.
            simpl.
            tauto.
          assert (exists hs' : Ensemble Formula, (forall h : Formula, In h ps <-> member h hs') /\ Infers hs' c).
            destruct H0 as [hs'].
            destruct H0.
            exists hs'.
            constructor.
            intros h.
            constructor.
            intro.
            apply H0.
            simpl.
            tauto.
            intro.
            assert (In h (a :: ps)).
              apply (proj2 (H0 h) H3).
            destruct H4.
            subst.
            apply i.
            apply H4.
            apply H2.
          assert (Infers (singleton (fold_right andB trueB ps)) c).
            apply (proj2 (IHps hs H1 c) H2).
          apply (cut_property (singleton (fold_right andB trueB (a :: ps)))  (fold_right andB trueB ps) c).
          simpl.
          apply (ConjunctionE2 _ a _).
          apply ByAssumption.
          apply Singleton.
          apply (extendInfers (singleton (fold_right andB trueB ps)) c H3).
          intros p.
          intro.
          apply UnionR.
          apply H4.
        * assert (forall p : Formula, In p ps -> member p (delete a hs)).
            intros p.
            intro.
            constructor.
            apply H.
            simpl.
            tauto.
            intro.
            inversion H2.
            subst.
            contradiction n.
          assert (exists hs' : Ensemble Formula, (forall h : Formula, In h ps <-> member h hs') /\ Infers hs' (ImplicationF a c)).
            destruct H0 as [hs'].
            destruct H0.
            exists (delete a hs').
            constructor.
            intros h.
            constructor.
            intro.
            constructor.
            apply H0.
            simpl.
            tauto.
            intro.
            inversion H4.
            subst.
            contradiction n.
            intro.
            destruct H3.
            assert (In h (a :: ps)).
              apply H0.
              apply H3.
            destruct H5.
            contradiction H4.
            subst.
            apply Singleton.
            apply H5.
            apply ImplicationI.
            apply (extendInfers hs' c H2).
            intros h.
            intro.
            destruct (eq_Formula_dec a h).
            subst.
            apply UnionR.
            apply Singleton.
            apply UnionL.
            constructor.
            apply H3.
            intro.
            contradiction n0.
            inversion H4.
            tauto.
          assert (Infers (singleton (fold_right andB trueB ps)) (ImplicationF a c)).
            apply (proj2 (IHps (delete a hs) H1 (ImplicationF a c)) H2).
          apply (ImplicationE _ a c).
          apply (cut_property (singleton (fold_right andB trueB (a :: ps))) (fold_right andB trueB ps) (ImplicationF a c)).
          simpl.
          apply (ConjunctionE2 _ a _).
          apply ByAssumption.
          apply Singleton.
          apply (extendInfers (singleton (fold_right andB trueB ps)) (ImplicationF a c) H3).
          intros p.
          intro.
          apply UnionR.
          apply H4.
          simpl.
          apply (ConjunctionE1 _ _ (fold_right ConjunctionF (ImplicationF ContradictionF ContradictionF) ps)).
          apply ByAssumption.
          apply Singleton.
    Qed.

  End LindenbaumBooleanAlgebra.

  Section Completeness.

    Instance LBA : CountableBooleanAlgebra Formula :=
      LindenbaumBooleanAlgebra
    .

    Lemma andBs_Infers :
      forall ps : list Formula,
      forall p : Formula,
      Infers (singleton (fold_right andB trueB ps)) p <-> (exists hs : Ensemble Formula, (forall h : Formula, In h ps <-> member h hs) /\ Infers hs p).
    Proof.
      intros ps.
      induction ps.
      - intros.
        simpl.
        constructor.
        * intro.
          exists empty.
          constructor.
          intros h.
          constructor.
          tauto.
          intro.
          inversion H0.
          apply (cut_property empty (ImplicationF ContradictionF ContradictionF) p).
          apply ImplicationI.
          apply ByAssumption.
          apply UnionR.
          apply Singleton.
          apply (extendInfers (singleton (ImplicationF ContradictionF ContradictionF)) p H).
          intros h.
          intro.
          apply UnionR.
          apply H0.
        * intro.
          destruct H as [hs].
          destruct H.
          apply (extendInfers hs p H0).
          intros h.
          intro.
          destruct (proj2 (H h) H1).
      - intros p.
        constructor.
        * intro.
          assert (exists hs : Ensemble Formula, (forall h : Formula, In h ps <-> member h hs) /\ Infers hs (ImplicationF a p)).
            apply IHps.
            apply ImplicationI.
            apply (cut_property (insert a (singleton (fold_right andB trueB ps))) (fold_right andB trueB (a :: ps)) p).
            simpl.
            apply ConjunctionI.
            apply ByAssumption.
            apply UnionR.
            apply Singleton.
            apply ByAssumption.
            apply UnionL.
            apply Singleton.
            apply (extendInfers (singleton (fold_right andB trueB (a :: ps))) p H).
            intros h.
            intro.
            apply UnionR.
            apply H0.
          destruct H0 as [hs].
          exists (insert a hs).
          constructor.
          intros h.
          simpl.
          destruct H0.
          constructor.
          intro.
          destruct H2.
          subst.
          apply UnionR.
          apply Singleton.
          apply UnionL.
          apply H0.
          apply H2.
          intro.
          inversion H2.
          subst.
          apply or_intror.
          apply H0.
          apply H3.
          subst.
          inversion H3.
          tauto.
          destruct H0.
          apply (cut_property (insert a hs) (ImplicationF a p) p).
          apply (extendInfers hs (ImplicationF a p) H1).
          intros h.
          intro.
          apply UnionL.
          apply H2.
          apply (ImplicationE _ a p).
          apply (extendInfers hs (ImplicationF a p) H1).
          intros h.
          intro.
          apply UnionL.
          apply UnionL.
          apply H2.
          apply ByAssumption.
          apply UnionL.
          apply UnionR.
          apply Singleton.
        * intro.
          destruct H as [hs].
          destruct H.
          destruct (in_dec eq_Formula_dec a ps).
          apply (cut_property (singleton (fold_right andB trueB (a :: ps))) (fold_right andB trueB ps) p).
          simpl.
          apply (ConjunctionE2 _ a _).
          apply ByAssumption.
          apply Singleton.
          apply (extendInfers (singleton (fold_right andB trueB ps)) p).
          apply IHps.
          exists hs.
          constructor.
          intros h.
          constructor.
          intro.
          apply H.
          simpl.
          tauto.
          destruct (eq_Formula_dec a h).
          intro.
          subst.
          apply i.
          intro.
          assert (In h (a :: ps)).
            apply H.
            apply H1.
          destruct H2.
          contradiction n.
          apply H2.
          apply H0.
          intros h.
          intro.
          apply UnionR.
          apply H1.
          assert (Infers (singleton (fold_right andB trueB ps)) (ImplicationF a p)).
            apply IHps.
            exists (delete a hs).
            constructor.
            intros h.
            constructor.
            intro.
            destruct (eq_Formula_dec h a).
            subst.
            contradiction n.
            constructor.
            apply H.
            intuition.
            intro.
            inversion H2.
            subst.
            tauto.
            intro.
            inversion H1.
            subst.
            assert (In h (a :: ps)).
              apply H.
            apply H2.
            destruct H4.
            contradiction H3.
            subst.
            apply Singleton.
            apply H4.
            apply ImplicationI.
            apply (extendInfers hs p H0).
            intros h.
            intro.
            destruct (eq_Formula_dec h a).
            subst.
            apply UnionR.
            apply Singleton.
            apply UnionL.
            constructor.
            apply H1.
            intro.
            inversion H2.
            subst.
            tauto.
          apply (cut_property (singleton (fold_right andB trueB (a :: ps))) (fold_right andB trueB ps) p).
          apply (ConjunctionE2 _ a _).
          apply ByAssumption.
          apply Singleton.
          apply (ImplicationE _ a p).
          apply (extendInfers (singleton (fold_right andB trueB ps)) (ImplicationF a p) H1).
          intros h.
          intro.
          apply UnionR.
          apply H2.
          apply (ConjunctionE1 _ _ (fold_right andB trueB ps)).
          apply ByAssumption.
          apply UnionL.
          apply Singleton.
    Qed.

    Inductive TH : Ensemble Formula -> Ensemble Formula :=
    | InTheory :
      forall hs : Ensemble Formula,
      forall c : Formula,
      Infers hs c ->
      member c (TH hs)
    .

    Lemma lemma_1_of_1_3_8 :
      forall bs : Ensemble Formula,
      isFilter Formula LBA (TH bs).
    Proof.
      intros bs.
      constructor.
      exists (ImplicationF ContradictionF ContradictionF).
      apply InTheory.
      apply ImplicationI.
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      constructor.
      intros b1 b2 H1 H2.
      destruct H1.
      apply InTheory.
      apply (cut_property hs c).
      apply H.
      apply (extendInfers (singleton c) b2).
      apply (proj1 (leq_LBA c b2) H2).
      intros p.
      intro.
      apply UnionR.
      apply H0.
      intros b1 b2 b H1 H2 H3.
      destruct H1.
      destruct H2.
      apply InTheory.
      apply (cut_property hs (ConjunctionF c c0)).
      apply ConjunctionI.
      apply H.
      apply H0.
      apply (extendInfers (singleton (ConjunctionF c c0)) b).
      destruct H3.
      apply H2.
      intros p.
      intro.
      apply UnionR.
      apply H1.
    Qed.

    Lemma Cl_subset_TH :
      forall hs : Ensemble Formula,
      isSubsetOf (Cl Formula LBA hs) (TH hs).
    Proof.
      intros hs.
      cut (
        forall ps : list Formula,
        (forall p : Formula, In p ps -> member p hs) ->
        forall c : Formula,
        eqB (andB (fold_right andB trueB ps) c) (fold_right andB trueB ps) ->
        (exists hs' : Ensemble Formula, isSubsetOf hs' hs /\ Infers hs' c)
      ).
        intro.
        intros p.
        intro.
        inversion H0.
        subst.
        destruct (H ps H1 p H2) as [hs'].
        destruct H3.
        apply InTheory.
        apply (extendInfers hs' p H4).
        apply H3.
      intros ps.
      intro.
      intros c.
      intro.
      assert (Infers (singleton (fold_right andB trueB ps)) c).
        apply leq_LBA.
        apply H0.
      destruct (proj1 (andBs_LBA ps hs H c) H1) as [hs'].
      exists hs'.
      destruct H2.
      constructor.
      intros h.
      intro.
      apply H.
      apply H2.
      apply H4.
      apply H3.
    Qed.

    Lemma Infers_has_compactness :
      forall hs : Ensemble Formula,
      forall c : Formula,
      Infers hs c ->
      exists ps : list Formula, (forall p : Formula, In p ps -> member p hs) /\ (exists hs' : Ensemble Formula, (forall h : Formula, In h ps <-> member h hs') /\ Infers hs' c).
    Proof.
      intros hs c.
      intro.
      induction H.
      - exists [h].
        constructor.
        intros p.
        intro.
        inversion H0.
        subst.
        apply H.
        inversion H1.
        exists (singleton h).
        constructor.
        intros p.
        constructor.
        intro.
        inversion H0.
        subst.
        apply Singleton.
        inversion H1.
        intro.
        inversion H0.
        subst.
        simpl.
        tauto.
        apply ByAssumption.
        apply Singleton.
      - destruct IHInfers1 as [ps1].
        destruct IHInfers2 as [ps2].
        destruct H1.
        destruct H2.
        destruct H3 as [hs1'].
        destruct H4 as [hs2'].
        destruct H3.
        destruct H4.
        exists (ps1 ++ ps2).
        constructor.
        apply (subset_append ps1 ps2 hs H1 H2).
        exists (union hs1' hs2').
        constructor.
        apply (in_append_iff_member_union ps1 ps2 hs1' hs2' H3 H4).
        apply (ContradictionI _ a).
        apply (extendInfers hs1' a H5).
        intros p.
        intro.
        apply UnionL.
        apply H7.
        apply (extendInfers hs2' (NegationF a) H6).
        intros p.
        intro.
        apply UnionR.
        apply H7.
      - destruct IHInfers as [ps].
        destruct H0.
        destruct H1 as [hs'].
        destruct H1.
        exists ps.
        constructor.
        apply H0.
        exists hs'.
        constructor.
        apply H1.
        apply ContradictionE.
        apply H2.
      - destruct IHInfers as [ps].
        destruct H0.
        destruct H1 as [hs'].
        destruct H1.
        exists (remove eq_Formula_dec a ps).
        constructor.
        apply subset_remove.
        apply H0.
        exists (delete a hs').
        constructor.
        apply in_remove_iff_member_delete.
        apply H1.
        apply NegationI.
        apply (extendInfers hs' ContradictionF H2).
        intros p.
        intro.
        destruct (eq_Formula_dec p a).
        apply UnionR.
        subst.
        apply Singleton.
        apply UnionL.
        constructor.
        apply H3.
        intro.
        inversion H4.
        subst.
        tauto.
      - destruct IHInfers as [ps].
        destruct H0.
        destruct H1 as [hs'].
        destruct H1.
        exists (remove eq_Formula_dec (NegationF a) ps).
        constructor.
        apply subset_remove.
        apply H0.
        exists (delete (NegationF a) hs').
        constructor.
        apply in_remove_iff_member_delete.
        apply H1.
        apply NegationE.
        apply (extendInfers hs' ContradictionF H2).
        intros p.
        intro.
        destruct (eq_Formula_dec p (NegationF a)).
        apply UnionR.
        subst.
        apply Singleton.
        apply UnionL.
        constructor.
        apply H3.
        intro.
        inversion H4.
        subst.
        tauto.
      - destruct IHInfers1 as [ps1].
        destruct IHInfers2 as [ps2].
        destruct H1.
        destruct H2.
        destruct H3 as [hs1'].
        destruct H4 as [hs2'].
        destruct H3.
        destruct H4.
        exists (ps1 ++ ps2).
        constructor.
        apply (subset_append ps1 ps2 hs H1 H2).
        exists (union hs1' hs2').
        constructor.
        apply (in_append_iff_member_union ps1 ps2 hs1' hs2' H3 H4).
        apply ConjunctionI.
        apply (extendInfers hs1' a H5).
        intros p.
        intro.
        apply UnionL.
        apply H7.
        apply (extendInfers hs2' b H6).
        intros p.
        intro.
        apply UnionR.
        apply H7.
      - destruct IHInfers as [ps].
        destruct H0.
        destruct H1 as [hs'].
        destruct H1.
        exists ps.
        constructor.
        apply H0.
        exists hs'.
        constructor.
        apply H1.
        apply (ConjunctionE1 _ a b).
        apply H2.
      - destruct IHInfers as [ps].
        destruct H0.
        destruct H1 as [hs'].
        destruct H1.
        exists ps.
        constructor.
        apply H0.
        exists hs'.
        constructor.
        apply H1.
        apply (ConjunctionE2 _ a b).
        apply H2.
      - destruct IHInfers as [ps].
        destruct H0.
        destruct H1 as [hs'].
        destruct H1.
        exists ps.
        constructor.
        apply H0.
        exists hs'.
        constructor.
        apply H1.
        apply (DisjunctionI1 _ a b).
        apply H2.
      - destruct IHInfers as [ps].
        destruct H0.
        destruct H1 as [hs'].
        destruct H1.
        exists ps.
        constructor.
        apply H0.
        exists hs'.
        constructor.
        apply H1.
        apply (DisjunctionI2 _ a b).
        apply H2.
      - destruct IHInfers1 as [ps1].
        destruct IHInfers2 as [ps2].
        destruct IHInfers3 as [ps3].
        destruct H2.
        destruct H3.
        destruct H4.
        destruct H5 as [hs1'].
        destruct H6 as [hs2'].
        destruct H7 as [hs3'].
        destruct H5.
        destruct H6.
        destruct H7.
        exists (ps1 ++ (remove eq_Formula_dec a ps2 ++ remove eq_Formula_dec b ps3)).
        constructor.
        apply subset_append.
        apply H2.
        apply subset_append.
        apply subset_remove.
        apply H3.
        apply subset_remove.
        apply H4.
        exists (union hs1' (union (delete a hs2') (delete b hs3'))).
        constructor.
        apply in_append_iff_member_union.
        apply H5.
        apply in_append_iff_member_union.
        apply in_remove_iff_member_delete.
        apply H6.
        apply in_remove_iff_member_delete.
        apply H7.
        apply (DisjunctionE _ a b c).
        apply (extendInfers hs1' (DisjunctionF a b) H8).
        intros p.
        intro.
        apply UnionL.
        apply H11.
        apply (extendInfers hs2' c H9).
        intros p.
        intro.
        destruct (eq_Formula_dec p a).
        apply UnionR.
        subst.
        apply Singleton.
        apply UnionL.
        apply UnionR.
        apply UnionL.
        constructor.
        apply H11.
        intro.
        apply n.
        inversion H12.
        tauto.
        apply (extendInfers hs3' c H10).
        intros p.
        intro.
        destruct (eq_Formula_dec p b).
        apply UnionR.
        subst.
        apply Singleton.
        apply UnionL.
        apply UnionR.
        apply UnionR.
        constructor.
        apply H11.
        intro.
        apply n.
        inversion H12.
        tauto.
      - destruct IHInfers as [ps].
        destruct H0.
        destruct H1 as [hs'].
        destruct H1.
        exists (remove eq_Formula_dec a ps).
        constructor.
        apply subset_remove.
        apply H0.
        exists (delete a hs').
        constructor.
        apply in_remove_iff_member_delete.
        apply H1.
        apply ImplicationI.
        apply (extendInfers hs' b H2).
        intros p.
        intro.
        destruct (eq_Formula_dec p a).
        apply UnionR.
        subst.
        apply Singleton.
        apply UnionL.
        constructor.
        apply H3.
        intro.
        inversion H4.
        subst.
        tauto.
      - destruct IHInfers1 as [ps1].
        destruct IHInfers2 as [ps2].
        destruct H1.
        destruct H2.
        destruct H3 as [hs1'].
        destruct H4 as [hs2'].
        destruct H3.
        destruct H4.
        exists (ps1 ++ ps2).
        constructor.
        apply (subset_append ps1 ps2 hs H1 H2).
        exists (union hs1' hs2').
        constructor.
        apply (in_append_iff_member_union ps1 ps2 hs1' hs2' H3 H4).
        apply (ImplicationE _ a b).
        apply (extendInfers hs1' (ImplicationF a b) H5).
        intros p.
        intro.
        apply UnionL.
        apply H7.
        apply (extendInfers hs2' a H6).
        intros p.
        intro.
        apply UnionR.
        apply H7.
      - destruct IHInfers1 as [ps1].
        destruct IHInfers2 as [ps2].
        destruct H1.
        destruct H2.
        destruct H3 as [hs1'].
        destruct H4 as [hs2'].
        destruct H3.
        destruct H4.
        exists (remove eq_Formula_dec a ps1 ++ remove eq_Formula_dec b ps2).
        constructor.
        apply subset_append.
        apply subset_remove.
        apply H1.
        apply subset_remove.
        apply H2.
        exists (union (delete a hs1') (delete b hs2')).
        constructor.
        apply in_append_iff_member_union.
        apply in_remove_iff_member_delete.
        apply H3.
        apply in_remove_iff_member_delete.
        apply H4.
        apply BiconditionalI.
        apply (extendInfers hs1' b H5).
        intros p.
        intro.
        destruct (eq_Formula_dec p a).
        apply UnionR.
        subst.
        apply Singleton.
        apply UnionL.
        apply UnionL.
        constructor.
        apply H7.
        intro.
        inversion H8.
        subst.
        tauto.
        apply (extendInfers hs2' a H6).
        intros p.
        intro.
        destruct (eq_Formula_dec p b).
        apply UnionR.
        subst.
        apply Singleton.
        apply UnionL.
        apply UnionR.
        constructor.
        apply H7.
        intro.
        inversion H8.
        subst.
        tauto.
      - destruct IHInfers1 as [ps1].
        destruct IHInfers2 as [ps2].
        destruct H1.
        destruct H2.
        destruct H3 as [hs1'].
        destruct H4 as [hs2'].
        destruct H3.
        destruct H4.
        exists (ps1 ++ ps2).
        constructor.
        apply (subset_append ps1 ps2 hs H1 H2).
        exists (union hs1' hs2').
        constructor.
        apply (in_append_iff_member_union ps1 ps2 hs1' hs2' H3 H4).
        apply (BiconditionalE1 _ a b).
        apply (extendInfers hs1' (BiconditionalF a b) H5).
        intros p.
        intro.
        apply UnionL.
        apply H7.
        apply (extendInfers hs2' a H6).
        intros p.
        intro.
        apply UnionR.
        apply H7.
      - destruct IHInfers1 as [ps1].
        destruct IHInfers2 as [ps2].
        destruct H1.
        destruct H2.
        destruct H3 as [hs1'].
        destruct H4 as [hs2'].
        destruct H3.
        destruct H4.
        exists (ps1 ++ ps2).
        constructor.
        apply (subset_append ps1 ps2 hs H1 H2).
        exists (union hs1' hs2').
        constructor.
        apply (in_append_iff_member_union ps1 ps2 hs1' hs2' H3 H4).
        apply (BiconditionalE2 _ a b).
        apply (extendInfers hs1' (BiconditionalF a b) H5).
        intros p.
        intro.
        apply UnionL.
        apply H7.
        apply (extendInfers hs2' b H6).
        intros p.
        intro.
        apply UnionR.
        apply H7.
    Qed.

    Lemma TH_subset_Cl :
      forall hs : Ensemble Formula,
      isSubsetOf (TH hs) (Cl Formula LBA hs).
    Proof.
      intros hs.
      intros c.
      intro.
      inversion H.
      subst.
      destruct (Infers_has_compactness hs c H0) as [ps].
      destruct H1.
      assert (Infers (singleton (fold_right andB trueB ps)) c).
        apply (proj2 (andBs_LBA ps hs H1 c) H2).
      apply (Closure Formula LBA ps).
      apply H1.
      apply leq_LBA.
      apply H3.
    Qed.

    Lemma bound_exists :
      forall ps : list Formula,
      exists bound : nat,
      forall p : Formula,
      In p ps ->
      exists n : nat, enumerateFormula n = p /\ n < bound.
    Proof.
      intros ps.
      induction ps.
      - exists 0.
        simpl.
        tauto.
      - destruct (Formula_is_enumerable a) as [bound1].
        destruct IHps as [bound2].
        assert (bound1 >= bound2 \/ bound1 < bound2).
          lia.
        destruct H1.
        exists (S bound1).
        intros p.
        simpl.
        intro.
        destruct H2.
        exists bound1.
        constructor.
        subst.
        tauto.
        lia.
        destruct (H0 p H2) as [n].
        exists n.
        destruct H3.
        constructor.
        apply H3.
        lia.
        exists bound2.
        intros p.
        intro.
        simpl.
        inversion H2.
        exists bound1.
        subst.
        constructor.
        tauto.
        tauto.
        destruct (H0 p H3) as [n].
        destruct H4.
        exists n.
        tauto.
    Qed.

    Definition Filter (hs : Ensemble Formula) (n : nat) : Ensemble Formula :=
      improveFilter Formula LBA (TH hs) n
    .

    Fixpoint AxmSet (hs : Ensemble Formula) (n : nat) : Ensemble Formula :=
      match n with
      | 0 => hs
      | S n' => union (AxmSet hs n') (Insert Formula LBA (Filter hs n') n')
      end
    .

    Lemma inconsistent_property_1 :
      forall hs : Ensemble Formula,
      Infers hs ContradictionF <-> inconsistent Formula LBA (Cl Formula LBA hs).
    Proof.
      intros hs.
      constructor.
      intro.
      exists ContradictionF.
      constructor.
      assert (isSubsetOf (TH hs) (Cl Formula LBA hs)).
        apply TH_subset_Cl.
      apply (H0 ContradictionF).
      apply InTheory.
      apply H.
      apply eqB_refl.
      intro.
      destruct H as [b'].
      destruct H.
      assert (member b' (TH hs)).
        apply (Cl_subset_TH hs b' H).
      inversion H1.
      subst.
      apply (cut_property hs b' ContradictionF).
      apply H2.
      destruct H0.
      apply (extendInfers (singleton b') ContradictionF H0).
      intros p.
      intro.
      apply UnionR.
      apply H4.
    Qed.

    Lemma equiconsistent_property_1 :
      forall hs1 : Ensemble Formula,
      forall hs2 : Ensemble Formula,
      isFilter Formula LBA hs1 ->
      isFilter Formula LBA hs2 ->
      equiconsistent Formula LBA hs1 hs2 <-> (Infers hs1 ContradictionF <-> Infers hs2 ContradictionF).
    Proof.
      intros hs1 hs2 HHH1 HHH2.
      constructor.
      intro.
      constructor.
      intro.
      apply inconsistent_property_1.
      apply (inconsistent_subset Formula LBA hs2).
      apply fact_3_of_1_2_8.
      apply H.
      apply (inconsistent_subset Formula LBA (Cl Formula LBA hs1)).
      apply fact_5_of_1_2_8.
      apply HHH1.
      apply inconsistent_property_1.
      apply H0.
      intro.
      apply inconsistent_property_1.
      apply (inconsistent_subset Formula LBA hs1).
      apply fact_3_of_1_2_8.
      apply H.
      apply (inconsistent_subset Formula LBA (Cl Formula LBA hs2)).
      apply fact_5_of_1_2_8.
      apply HHH2.
      apply inconsistent_property_1.
      apply H0.
      intro.
      constructor.
      intro.
      apply (inconsistent_subset Formula LBA (Cl Formula LBA hs2)).
      apply fact_5_of_1_2_8.
      apply HHH2.
      apply inconsistent_property_1.
      apply H.
      apply inconsistent_property_1.
      apply (inconsistent_subset Formula LBA hs1).
      apply fact_3_of_1_2_8.
      apply H0.
      intro.
      apply (inconsistent_subset Formula LBA (Cl Formula LBA hs1)).
      apply fact_5_of_1_2_8.
      apply HHH1.
      apply inconsistent_property_1.
      apply H.
      apply inconsistent_property_1.
      apply (inconsistent_subset Formula LBA hs2).
      apply fact_3_of_1_2_8.
      apply H0.
    Qed.

    Lemma lemma_1_of_1_3_9 :
      forall hs : Ensemble Formula,
      forall n : nat,
      isSubsetOf (Filter hs n) (TH (AxmSet hs n)) /\ isSubsetOf (TH (AxmSet hs n)) (Filter hs n).
    Proof.
      intros hs n.
      induction n.
      - unfold Filter in *.
        simpl.
        unfold isSubsetOf.
        intuition.
      - destruct IHn.
        unfold Filter in *.
        simpl.
        constructor.
        * assert (isSubsetOf (Cl Formula LBA (union (improveFilter Formula LBA (TH hs) n) (Insert Formula LBA (improveFilter Formula LBA (TH hs) n) n))) (Cl Formula LBA (TH (union (AxmSet hs n) (Insert Formula LBA (Filter hs n) n))))).
            apply fact_4_of_1_2_8.
            intros b.
            intro.
            inversion H1.
            subst.
            assert (member b (TH (AxmSet hs n))).
              apply (H b H2).
            inversion H3.
            subst.
            apply InTheory.
            apply (extendInfers (AxmSet hs n) b H4).
            intros p.
            intro.
            apply UnionL.
            apply H5.
            subst.
            apply InTheory.
            apply ByAssumption.
            apply UnionR.
            apply H2.
          assert (isSubsetOf (Cl Formula LBA (TH (union (AxmSet hs n) (Insert Formula LBA (Filter hs n) n)))) (TH (union (AxmSet hs n) (Insert Formula LBA (Filter hs n) n)))).
            apply fact_5_of_1_2_8.
            apply lemma_1_of_1_3_8.
          unfold isSubsetOf in *.
          intuition.
        * cut (isSubsetOf (Cl Formula LBA (union (AxmSet hs n) (Insert Formula LBA (Filter hs n) n))) (Cl Formula LBA (union (improveFilter Formula LBA (TH hs) n) (Insert Formula LBA (improveFilter Formula LBA (TH hs) n) n)))).
            intro.
            assert (isSubsetOf (TH (union (AxmSet hs n) (Insert Formula LBA (Filter hs n) n))) (Cl Formula LBA (union (AxmSet hs n) (Insert Formula LBA (Filter hs n) n)))).
              apply TH_subset_Cl.
            unfold isSubsetOf in *.
            intuition.
          assert (isSubsetOf (Cl Formula LBA (Cl Formula LBA (union (improveFilter Formula LBA (TH hs) n) (Insert Formula LBA (improveFilter Formula LBA (TH hs) n) n)))) (Cl Formula LBA (union (improveFilter Formula LBA (TH hs) n) (Insert Formula LBA (improveFilter Formula LBA (TH hs) n) n)))).
            apply fact_5_of_1_2_8.
            apply fact_1_of_1_2_8.
          cut (isSubsetOf (Cl Formula LBA (union (AxmSet hs n) (Insert Formula LBA (Filter hs n) n))) (Cl Formula LBA (Cl Formula LBA (union (improveFilter Formula LBA (TH hs) n) (Insert Formula LBA (improveFilter Formula LBA (TH hs) n) n))))).
            unfold isSubsetOf in *.
            intuition.
          apply fact_4_of_1_2_8.
          intros b.
          intro.
          inversion H2.
          subst.
          apply (Closure Formula LBA [b]).
          intros p.
          intro.
          inversion H4.
          subst.
          apply UnionL.
          apply (H0 p).
          apply InTheory.
          apply ByAssumption.
          apply H3.
          inversion H5.
          apply leq_LBA.
          simpl.
          apply (ConjunctionE1 _ b (ImplicationF ContradictionF ContradictionF)).
          apply ByAssumption.
          apply Singleton.
          subst.
          inversion H3.
          subst.
          apply (Closure Formula LBA [enumB n]).
          intros p.
          intro.
          inversion H5.
          subst.
          apply UnionR.
          apply Insertion.
          apply H4.
          inversion H6.
          apply leq_LBA.
          simpl.
          apply (ConjunctionE1 _ (enumerateFormula n) (ImplicationF ContradictionF ContradictionF)).
          apply ByAssumption.
          apply Singleton.
    Qed.

    Lemma RequirementForCompleteness :
      forall hs : Ensemble Formula,
      forall c : Formula,
      Entails hs c ->
      forall v : Formula -> Prop,
      isStructure v ->
      equiconsistent Formula LBA (TH (insert (NegationF c) hs)) v ->
      isSubsetOf (TH (insert (NegationF c) hs)) v ->
      isFilter Formula LBA v ->
      Infers hs c.
    Proof.
      intros hs c.
      intro Entailment.
      intros v.
      intro IsStructure.
      intro Equiconsistent.
      intro Extensionality.
      intro IsFilter.
      apply NegationE.
      assert (inconsistent Formula LBA (TH (insert (NegationF c) hs))).
        apply Equiconsistent.
        assert (inconsistent Formula LBA (Cl Formula LBA v)).
          apply inconsistent_property_1.
          apply (ContradictionI _ c).
          apply ByAssumption.
          apply Entailment.
          apply IsStructure.
          intros h.
          intro.
          apply Extensionality.
          apply InTheory.
          apply ByAssumption.
          apply UnionL.
          apply H.
          apply ByAssumption.
          apply Extensionality.
          apply InTheory.
          apply ByAssumption.
          apply UnionR.
          apply Singleton.
        apply (inconsistent_subset Formula LBA (Cl Formula LBA v) v).
        apply fact_5_of_1_2_8.
        apply IsFilter.
        apply H.
      assert (inconsistent Formula LBA (Cl Formula LBA (insert (NegationF c) hs))).
        apply (inconsistent_subset Formula LBA (TH (insert (NegationF c) hs))).
        apply TH_subset_Cl.
        apply H.
      apply inconsistent_property_1.
      apply H0.
    Qed.

    Definition MaximalConsistentSet (bs : Ensemble Formula) : Ensemble Formula :=
      CompleteFilter Formula LBA (TH bs)
    .

    Inductive FullAxmSet : Ensemble Formula -> Ensemble Formula :=
    | InFullAxmSet :
      forall n : nat,
      forall bs : Ensemble Formula,
      forall b : Formula,
      member b (AxmSet bs n) ->
      member b (FullAxmSet bs)
    .

    Lemma lemma_2_of_1_3_9 :
      forall bs : Ensemble Formula,
      isSubsetOf (MaximalConsistentSet bs) (TH (FullAxmSet bs)).
    Proof.
      intros bs.
      intros p.
      intro.
      inversion H.
      subst.
      assert (member p (TH (AxmSet bs n))).
        apply (proj1 (lemma_1_of_1_3_9 bs n) p H0).
      inversion H1.
      subst.
      apply InTheory.
      apply (extendInfers (AxmSet bs n) p H2).
      intros b.
      intro.
      apply (InFullAxmSet n).
      apply H3.
    Qed.

    Lemma lemma_3_of_1_3_9 :
      forall bs : Ensemble Formula,
      isSubsetOf (TH (FullAxmSet bs)) (MaximalConsistentSet bs).
    Proof.
      intros bs.
      cut (
        forall ps : list Formula,
        (forall p : Formula, In p ps -> member p (FullAxmSet bs)) ->
        exists m : nat,
        (forall p : Formula, In p ps -> member p (Filter bs m))
      ).
        intro.
        intros p.
        intro.
        inversion H0.
        subst.
        destruct (Infers_has_compactness (FullAxmSet bs) p H1) as [ps].
        destruct H2.
        destruct (H ps H2) as [m].
        apply (InCompleteFilter Formula LBA m).
        assert (isFilter Formula LBA (improveFilter Formula LBA (TH bs) m)).
          apply lemma_1_of_1_2_11.
          apply lemma_1_of_1_3_8.
        inversion H5.
        destruct H7.
        apply (H7 (fold_right andB trueB ps) p).
        apply (fact_5_of_1_2_8 Formula LBA (improveFilter Formula LBA (TH bs) m) H5 (fold_right andB trueB ps)).
        apply (Closure Formula LBA ps).
        apply H4.
        apply andB_idempotent.
        apply leq_LBA.
        apply andBs_Infers.
        apply H3.
      intros ps.
      induction ps.
      - intro.
        exists 0.
        simpl.
        tauto.
      - intro.
        assert (forall p : Formula, In p ps -> member p (FullAxmSet bs)).
          intros p.
          intro.
          apply H.
          simpl.
          tauto.
        assert (member a (FullAxmSet bs)).
          apply H.
          simpl.
          tauto.
        inversion H1.
        subst.
        assert (member a (Filter bs n)).
          apply (proj2 (lemma_1_of_1_3_9 bs n) a).
          apply InTheory.
          apply ByAssumption.
          apply H2.
        destruct (IHps H0) as [n'].
        assert (n >= n' \/ n < n').
          lia.
        destruct H5.
        exists n.
        intros p.
        simpl.
        intro.
        destruct H6.
        subst.
        apply H3.
        apply (lemma_1_of_1_2_12 Formula LBA (TH bs) n' n H5 p (H4 p H6)).
        exists n'.
        simpl.
        intro.
        intro.
        destruct H6.
        assert (n <= n').
          lia.
        subst.
        apply (lemma_1_of_1_2_12 Formula LBA (TH bs) n n' H7 p H3).
        apply (H4 p H6).
    Qed.

    Definition isMetaDN (bs : Ensemble Formula) : Prop :=
      forall p1 : Formula, (member (NegationF p1) bs -> member ContradictionF bs) -> member p1 bs
    .

    Definition isImplicationFaithful (bs : Ensemble Formula) : Prop :=
      forall p1 : Formula, forall p2 : Formula, member (ImplicationF p1 p2) bs <-> (member p1 bs -> member p2 bs)
    .

    Theorem theorem_1_3_10 :
      forall bs : Ensemble Formula,
      isSubsetOf (TH bs) (MaximalConsistentSet bs) /\ equiconsistent Formula LBA (TH bs) (MaximalConsistentSet bs) /\ (forall p : Formula, member p (MaximalConsistentSet bs) <-> Infers (MaximalConsistentSet bs) p) /\ isMetaDN (MaximalConsistentSet bs) /\ isImplicationFaithful (MaximalConsistentSet bs).
    Proof.
      intros bs.
      constructor.
      apply theorem_1_2_14.
      apply lemma_1_of_1_3_8.
      constructor.
      apply lemma_3_of_1_2_13.
      apply lemma_1_of_1_3_8.
      assert (
        forall p : Formula,
        member p (MaximalConsistentSet bs) <-> Infers (MaximalConsistentSet bs) p
      ).
        intros p.
        constructor.
        intro.
        assert (member p (TH (MaximalConsistentSet bs))).
          apply Cl_subset_TH.
          apply fact_3_of_1_2_8.
          apply H.
        inversion H0.
        subst.
        apply H1.
        intro.
        apply (fact_5_of_1_2_8 Formula LBA (MaximalConsistentSet bs)).
        apply theorem_1_2_14.
        apply lemma_1_of_1_3_8.
        apply TH_subset_Cl.
        apply InTheory.
        apply H.
      constructor.
      apply H.
      assert (isComplete Formula LBA (MaximalConsistentSet bs)).
        apply theorem_1_2_14.
        apply lemma_1_of_1_3_8.
      assert (isMetaDN (MaximalConsistentSet bs)).
        intros p1.
        intro.
        apply (H0 p1).
        constructor.
        apply inconsistent_subset.
        assert (isSubsetOf (MaximalConsistentSet bs) (insert p1 (MaximalConsistentSet bs))).
          intros h.
          intro.
          apply UnionL.
          apply H2.
        assert (isSubsetOf (insert p1 (MaximalConsistentSet bs)) (Cl Formula LBA (insert p1 (MaximalConsistentSet bs)))).
          apply fact_3_of_1_2_8.
        unfold isSubsetOf in *.
        intuition.
        intro.
        assert (Infers (insert p1 (MaximalConsistentSet bs)) ContradictionF).
          apply inconsistent_property_1.
          apply H2.
        exists ContradictionF.
        constructor.
        apply H1.
        apply H.
        apply NegationI.
        apply H3.
        apply eqB_refl.
      constructor.
      apply H1.
      intros p1 p2.
      constructor.
      intro.
      intro.
      apply H.
      apply (ImplicationE (MaximalConsistentSet bs) p1 p2).
      apply H.
      apply H2.
      apply H.
      apply H3.
      intro.
      apply H1.
      intro.
      apply H.
      assert (Infers (insert (ImplicationF p1 p2) (MaximalConsistentSet bs)) ContradictionF).
        apply (ContradictionI (insert (ImplicationF p1 p2) (MaximalConsistentSet bs)) (ImplicationF p1 p2)).
        apply ByAssumption.
        apply UnionR.
        apply Singleton.
        apply (extendInfers (MaximalConsistentSet bs) (NegationF (ImplicationF p1 p2))).
        apply H.
        apply H3.
        intros h.
        intro.
        apply UnionL.
        apply H4.
      assert (Infers (MaximalConsistentSet bs) (ConjunctionF p1 (NegationF p2))).
        apply (DisjunctionE _ p1 (NegationF p1)).
        apply (extendInfers empty (DisjunctionF p1 (NegationF p1)) (ExclusiveMiddle p1)).
        intros h.
        intro.
        inversion H5.
        apply (DisjunctionE _ p2 (NegationF p2)).
        apply (extendInfers empty (DisjunctionF p2 (NegationF p2)) (ExclusiveMiddle p2)).
        intros h.
        intro.
        inversion H5.
        apply ContradictionE.
        apply (cut_property _ (ImplicationF p1 p2)).
        apply ImplicationI.
        apply ByAssumption.
        apply UnionL.
        apply UnionR.
        apply Singleton.
        apply (extendInfers (insert (ImplicationF p1 p2) (MaximalConsistentSet bs)) ContradictionF H4).
        intros h.
        intro.
        inversion H5.
        subst.
        apply UnionL.
        apply UnionL.
        apply UnionL.
        apply H6.
        subst.
        apply UnionR.
        apply H6.
        apply ConjunctionI.
        apply ByAssumption.
        apply UnionL.
        apply UnionR.
        apply Singleton.
        apply ByAssumption.
        apply UnionR.
        apply Singleton.
        apply (DisjunctionE _ p2 (NegationF p2)).
        apply (extendInfers empty (DisjunctionF p2 (NegationF p2)) (ExclusiveMiddle p2)).
        intros h.
        intro.
        inversion H5.
        apply ContradictionE.
        apply (cut_property _ (ImplicationF p1 p2)).
        apply ImplicationI.
        apply ByAssumption.
        apply UnionL.
        apply UnionR.
        apply Singleton.
        apply (extendInfers (insert (ImplicationF p1 p2) (MaximalConsistentSet bs)) ContradictionF H4).
        intros h.
        intro.
        inversion H5.
        subst.
        apply UnionL.
        apply UnionL.
        apply UnionL.
        apply H6.
        subst.
        apply UnionR.
        apply H6.
        apply ContradictionE.
        apply (cut_property _ (ImplicationF p1 p2)).
        apply ImplicationI.
        apply ContradictionE.
        apply (ContradictionI _ p1).
        apply ByAssumption.
        apply UnionR.
        apply Singleton.
        apply ByAssumption.
        apply UnionL.
        apply UnionL.
        apply UnionR.
        apply Singleton.
        apply (extendInfers (insert (ImplicationF p1 p2) (MaximalConsistentSet bs)) ContradictionF H4).
        intros h.
        intro.
        inversion H5.
        subst.
        apply UnionL.
        apply UnionL.
        apply UnionL.
        apply H6.
        subst.
        apply UnionR.
        apply H6.
      assert (Infers (MaximalConsistentSet bs) p1).
        apply (ConjunctionE1 _ p1 (NegationF p2)).
        apply H5.
      assert (Infers (MaximalConsistentSet bs) (NegationF p2)).
        apply (ConjunctionE2 _ p1 (NegationF p2)).
        apply H5.
      apply (ContradictionI _ p2).
      apply H.
      apply H2.
      apply H.
      apply H6.
      apply H7.
    Qed.

    Parameter exclusive_middle : forall P : Prop, P \/ ~ P.

    Lemma ModelExistsIfConsistent :
      forall bs : Ensemble Formula,
      ~ Infers bs ContradictionF ->
      isStructure (MaximalConsistentSet bs).
    Proof.
      intros bs.
      intro.
      assert (forall p : Formula, satisfies (MaximalConsistentSet bs) p <-> Infers (MaximalConsistentSet bs) p).
        apply theorem_1_3_10.
      assert (Infers (MaximalConsistentSet bs) ContradictionF <-> inconsistent Formula LBA (MaximalConsistentSet bs)).
        assert (inconsistent Formula LBA (MaximalConsistentSet bs) <-> inconsistent Formula LBA (Cl Formula LBA (MaximalConsistentSet bs))).
          apply equiconsistent_property_1.
          apply theorem_1_2_14.
          apply lemma_1_of_1_3_8.
          apply fact_1_of_1_2_8.
        constructor.
        intro.
        apply (extendInfers (MaximalConsistentSet bs) ContradictionF H1).
        apply fact_3_of_1_2_8.
        intro.
        apply (extendInfers (Cl Formula LBA (MaximalConsistentSet bs)) ContradictionF H1).
        apply fact_5_of_1_2_8.
        apply theorem_1_2_14.
        apply lemma_1_of_1_3_8.
        assert (Infers (MaximalConsistentSet bs) ContradictionF <-> inconsistent Formula LBA (Cl Formula LBA (MaximalConsistentSet bs))).
          apply inconsistent_property_1.
        intuition.
      assert (~ inconsistent Formula LBA (MaximalConsistentSet bs)).
        intro.
        apply H.
        assert (inconsistent Formula LBA (TH bs)).
          apply lemma_3_of_1_2_13.
          apply lemma_1_of_1_3_8.
          apply H2.
        assert (Infers (TH bs) ContradictionF).
          apply inconsistent_property_1.
          apply (inconsistent_subset Formula LBA (TH bs) (Cl Formula LBA (TH bs))).
          apply fact_3_of_1_2_8.
          apply H3.
        assert (member ContradictionF (TH (TH bs))).
          apply InTheory.
          apply H4.
        assert (member ContradictionF (TH bs)).
          apply (fact_5_of_1_2_8 Formula LBA (TH bs)).
          apply lemma_1_of_1_3_8.
          apply TH_subset_Cl.
          apply H5.
        inversion H6.
        subst.
        apply H7.
        assert (isMetaDN (MaximalConsistentSet bs) /\ isImplicationFaithful (MaximalConsistentSet bs)).
          apply theorem_1_3_10.
      destruct H3.
      constructor.
      constructor.
      intro.
      apply H2.
      apply H1.
      apply H0.
      apply H5.
      tauto.
      constructor.
      intros p1.
      constructor.
      intro.
      intro.
      apply H2.
      apply H1.
      apply (ContradictionI _ p1).
      apply H0.
      apply H6.
      apply H0.
      apply H5.
      intro.
      apply H3.
      intro.
      contradiction H5.
      apply H0.
      apply NegationE.
      apply (ContradictionI _ (NegationF p1)).
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply (extendInfers (MaximalConsistentSet bs)).
      apply H0.
      apply H6.
      intros p.
      intro.
      apply UnionL.
      apply H7.
      constructor.
      intros p1 p2.
      constructor.
      intro.
      constructor.
      apply H0.
      apply (ConjunctionE1 _ p1 p2).
      apply H0.
      apply H5.
      apply H0.
      apply (ConjunctionE2 _ p1 p2).
      apply H0.
      apply H5.
      intro.
      destruct H5.
      apply H0.
      apply ConjunctionI.
      apply H0.
      apply H5.
      apply H0.
      apply H6.
      constructor.
      intros p1 p2.
      constructor.
      intro.
      destruct (exclusive_middle (satisfies (MaximalConsistentSet bs) p1)).
      apply or_introl.
      apply H6.
      apply or_intror.
      assert (Infers (MaximalConsistentSet bs) (NegationF p1)).
        apply H0.
        apply H3.
        intro.
        contradiction H6.
        apply H0.
        apply NegationE.
        apply (ContradictionI _ (NegationF p1)).
        apply ByAssumption.
        apply UnionR.
        apply Singleton.
        apply ByAssumption.
        apply UnionL.
        apply H7.
      apply H0.
      apply (DisjunctionE _ p1 p2).
      apply H0.
      apply H5.
      apply ContradictionE.
      apply (ContradictionI _ p1).
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply ByAssumption.
      apply UnionL.
      apply H0.
      apply H7.
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      intro.
      destruct H5.
      apply H0.
      apply DisjunctionI1.
      apply H0.
      apply H5.
      apply H0.
      apply DisjunctionI2.
      apply H0.
      apply H5.
      constructor.
      intros p1 p2.
      constructor.
      apply H4.
      apply H4.
      constructor.
      intros p1 p2.
      constructor.
      intro.
      constructor.
      apply H4.
      apply H0.
      apply ImplicationI.
      apply (BiconditionalE1 _ p1 p2).
      apply ByAssumption.
      apply UnionL.
      apply H5.
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply H4.
      apply H0.
      apply ImplicationI.
      apply (BiconditionalE2 _ p1 p2).
      apply ByAssumption.
      apply UnionL.
      apply H5.
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      intro.
      assert (satisfies (MaximalConsistentSet bs) (ImplicationF p1 p2)).
        apply H4.
        apply H5.
      assert (satisfies (MaximalConsistentSet bs) (ImplicationF p2 p1)).
        apply H4.
        apply H5.
      apply H0.
      apply BiconditionalI.
      apply (ImplicationE _ p1 p2).
      apply ByAssumption.
      apply UnionL.
      apply H6.
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply (ImplicationE _ p2 p1).
      apply ByAssumption.
      apply UnionL.
      apply H7.
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      intros p1.
      intro.
      apply H3.
      intro.
      apply H0.
      apply (ContradictionI _ (NegationF p1)).
      apply ByAssumption.
      apply H6.
      apply ByAssumption.
      apply H5.
    Qed.

    Corollary Completeness :
      forall hs : Ensemble Formula,
      forall c : Formula,
      Entails hs c ->
      Infers hs c.
    Proof.
      intros hs c.
      intro.
      destruct (exclusive_middle (Infers hs c)).
      apply H0.
      apply (RequirementForCompleteness hs c H (MaximalConsistentSet (insert (NegationF c) hs))).
      apply ModelExistsIfConsistent.
      intro.
      apply H0.
      apply NegationE.
      apply H1.
      apply lemma_3_of_1_2_13.
      apply lemma_1_of_1_3_8.
      apply theorem_1_2_14.
      apply lemma_1_of_1_3_8.
      apply theorem_1_2_14.
      apply lemma_1_of_1_3_8.
    Qed.

  End Completeness.

  Section Compactness.

    Theorem Entails_has_compactness :
      forall hs : Ensemble Formula,
      forall c : Formula,
      Entails hs c ->
      exists ps : list Formula, (forall p : Formula, In p ps -> member p hs) /\ (exists hs' : Ensemble Formula, (forall h : Formula, In h ps <-> member h hs') /\ Entails hs' c).
    Proof.
      intros hs c.
      intro.
      assert (Infers hs c).
        apply Completeness.
        apply H.
      destruct (Infers_has_compactness hs c H0) as [ps].
      exists ps.
      destruct H1.
      constructor.
      apply H1.
      destruct H2 as [hs'].
      exists hs'.
      destruct H2.
      constructor.
      apply H2.
      apply Soundness.
      apply H3.
    Qed.

  End Compactness.

End PropositionalLogic.

(* Praise the God! *)
