Require Export TopologicalSpaces Homeomorphisms SubspaceTopology.
From ZornsLemma Require Import EnsemblesTactics.

Definition clopen {X:TopologicalSpace} (S:Ensemble (point_set X))
  : Prop :=
  open S /\ closed S.

Definition connected (X:TopologicalSpace) : Prop :=
  forall S:Ensemble (point_set X), clopen S ->
        S = Empty_set \/ S = Full_set.

Lemma connected_img: forall {X Y:TopologicalSpace}
  (f:point_set X -> point_set Y),
  connected X -> continuous f -> surjective f -> connected Y.
Proof.
intros.
red.
intros.
destruct (H (inverse_image f S)).
- split.
  + apply H0, H2.
  + red.
    rewrite <- inverse_image_complement.
    apply H0, H2.
- left.
  extensionality_ensembles.
  destruct (H1 x).
  eapply False_ind, Noone_in_empty.
  rewrite <- H3.
  constructor.
  now rewrite H5.
- right.
  extensionality_ensembles.
  + constructor.
  + destruct (H1 x).
    rewrite <- H4.
    apply in_inverse_image.
    now rewrite H3.
Qed.

Lemma connected_union: forall {X:TopologicalSpace}
  {A:Type} (S:IndexedFamily A (point_set X)),
  (forall a:A, connected (SubspaceTopology (S a))) ->
  Inhabited (IndexedIntersection S) ->
  IndexedUnion S = Full_set -> connected X.
Proof.
intros.
pose (inc := fun (a:A) => subspace_inc (S a)).
destruct H0, H0.
red; intros.

assert (forall a:A, clopen (inverse_image (inc a) S0)).
{ intro.
  split.
  - apply subspace_inc_continuous, H2.
  - red.
    rewrite <- inverse_image_complement.
    apply subspace_inc_continuous, H2. }

destruct (classic (In S0 x)).
- right.
  assert (forall a:A, inverse_image (inc a) S0 = Full_set).
{ intro.
  destruct (H a _ (H3 a)).
  - assert (In (@Empty_set (point_set (SubspaceTopology (S a))))
      (exist _ x (H0 a))).
  { rewrite <- H5.
    now constructor. }
    now destruct H6.
  - assumption. }
  extensionality_ensembles.
  + constructor.
  + assert (In (IndexedUnion S) x0).
  { rewrite H1. constructor. }
    destruct H6.
    assert (In (@Full_set (point_set (SubspaceTopology (S a))))
      (exist _ x0 H6)) by
      constructor.
    rewrite <- H5 in H7.
    now destruct H7.

- left.
  assert (forall a:A, inverse_image (inc a) S0 = Empty_set).
{ intros.
  destruct (H a _ (H3 a)).
  - assumption.
  - assert (In (@Full_set (point_set (SubspaceTopology (S a))))
      (exist _ x (H0 a))) by
      constructor.
    rewrite <- H5 in H6.
    destruct H6.
    contradiction H4. }
  extensionality_ensembles.
  assert (In (IndexedUnion S) x0).
{ rewrite H1. constructor. }
  destruct H7.
  assert (In (@Empty_set (point_set (SubspaceTopology (S a))))
    (exist _ x0 H7)).
{ rewrite <- H5.
  now constructor. }
  destruct H8.
Qed.

Lemma topological_property_connected :
  topological_property connected.
Proof.
intros X Y f [g Hcont_f Hcont_g Hgf Hfg] Hconn S [Hopen Hclose].
destruct (Hconn (inverse_image f S));
[ | left | right ];
  try extensionality_ensembles.
- split; red.
  + now apply Hcont_f.
  + rewrite <- inverse_image_complement.
    now apply Hcont_f.
- rewrite <- Hfg.
  apply in_inverse_image.
  rewrite inverse_image_empty, <- H.
  constructor.
  now rewrite Hfg.
- constructor.
- rewrite <- Hfg.
  apply in_inverse_image.
  rewrite H.
  constructor.
Qed.
