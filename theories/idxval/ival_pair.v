From discprob.basic Require Import base sval order monad bigop_ext nify.
From mathcomp Require Import ssrfun ssreflect eqtype ssrbool seq fintype choice.
From discprob.prob Require Import prob countable finite stochastic_order rearrange.
Require Import Reals Psatz.
From discprob.idxval Require Import ival ival_dist.

Record ival_couplingP {A1 A2} (Is1: ival A1) (Is2: ival A2) (P: A1 → A2 → Prop) : Type :=
  mkICoupling { ic_witness :> ival {xy: A1 * A2 | P (fst xy) (snd xy)};
     ic_proj1: eq_ival Is1 (x ← ic_witness; mret (fst (sval x)));
     ic_proj2: eq_ival Is2 (x ← ic_witness; mret (snd (sval x)));
     }.

Record idist_couplingP {A1 A2} (Is1: ivdist A1) (Is2: ivdist A2) (P: A1 → A2 → Prop) : Type :=
  mkIdCoupling { idc_witness :> ivdist {xy: A1 * A2 | P (fst xy) (snd xy)};
     idc_proj1: eq_ivd Is1 (x ← idc_witness; mret (fst (sval x)));
     idc_proj2: eq_ivd Is2 (x ← idc_witness; mret (snd (sval x)));
     }.
From mathcomp Require Import bigop.

Lemma ic_coupling_to_id {A1 A2} (I1: ivdist A1) (I2: ivdist A2) P: 
  ival_couplingP I1 I2 P → 
  idist_couplingP I1 I2 P.
Proof.
  intros [Ic Hproj1 Hproj2].
  assert (Hsum1: is_series (countable_sum (ival.val Ic)) 1%R).
  {
    replace 1%R with R1 by auto.
    eapply (eq_ival_series _ _) in Hproj1; last eapply val_sum1.
    unshelve (eapply (countable_series_rearrange_covering_match _ _); last eassumption).
    { intros ic. rewrite //=. exists (existT (sval ic) tt).
      { abstract (rewrite Rmult_1_r => //=; destruct ic => //=). }
    }
    - apply val_nonneg. 
    - apply val_nonneg. 
    - intros (n1&?) (n2&?) Heq. apply sval_inj_pred => //=.
      inversion Heq. auto.
    - intros ((n1&[])&Hpf) => //=.
      unshelve (eexists).
      { exists n1.  rewrite //= Rmult_1_r // in Hpf. }
      apply sval_inj_pred => //=.
    - intros (n1&Hpf) => //=. nra.
  }
  exists {| ivd_ival := Ic; val_sum1 := Hsum1 |}; auto.
Qed.

Local Open Scope R_scope.
Record ival_coupling_nondepP {A1 A2} (Is1: ival A1) (Is2: ival A2) (P: A1 → A2 → Prop) : Type :=
  mkNonDepICoupling { ic_nondep_witness :> ival (A1 * A2);
               ic_nondep_support :
                 ∀ xy, (∃ i, ind ic_nondep_witness i = xy
                            ∧ val ic_nondep_witness i > 0) → P (fst xy) (snd xy);
     ic_nondep_proj1: eq_ival Is1 (x ← ic_nondep_witness; mret (fst x));
     ic_nondep_proj2: eq_ival Is2 (x ← ic_nondep_witness; mret (snd x));
     }.

Lemma ival_coupling_nondep_suffice {A1 A2} Is1 Is2 (P: A1 → A2 → Prop):
      ival_coupling_nondepP Is1 Is2 P →
      ival_couplingP Is1 Is2 P.
Proof.
  intros [Ic Isupp Hp1 Hp2].
  exists (ival_equip Ic _ Isupp).
  - setoid_rewrite Hp1.   
    setoid_rewrite (ival_bind_P Ic). 
    eapply ival_bind_congr; first reflexivity.
    intros (a1&a2) => //=; reflexivity.
  - setoid_rewrite Hp2.
    setoid_rewrite (ival_bind_P Ic). 
    eapply ival_bind_congr; first reflexivity.
    intros (a1&a2) => //=; reflexivity.
Qed.

Lemma ival_coupling_refl {A} (I: ival A) : ival_couplingP I I (λ x y, x = y).
Proof.
  unshelve (eexists).
  { refine (x ← I; mret (exist _ (x, x) _)). 
    done. }
  - setoid_rewrite ival_bind_mret_mret. setoid_rewrite ival_right_id. reflexivity.
  - setoid_rewrite ival_bind_mret_mret. setoid_rewrite ival_right_id. reflexivity.
Qed.

Lemma ival_coupling_sym {A1 A2} (Is1: ival A1) (Is2: ival A2) P
      (Ic: ival_couplingP Is1 Is2 P): ival_couplingP Is2 Is1 (λ x y, P y x).
Proof.
  destruct Ic as [Ic Hp1 Hp2].
  unshelve (eexists).
  { refine (mbind _ Ic). intros ((x&y)&HP).
    refine (mret (exist _ (y, x) _)); auto. }
  * setoid_rewrite Hp2. setoid_rewrite ival_assoc. apply ival_bind_congr; first by reflexivity.
    intros ((x&y)&Hpf). setoid_rewrite ival_left_id => //=. reflexivity.
  * setoid_rewrite Hp1. setoid_rewrite ival_assoc; apply ival_bind_congr; first by reflexivity.
    intros ((x&y)&Hpf). setoid_rewrite ival_left_id => //=. reflexivity.
Qed.
    
Lemma ival_coupling_eq {A} (Is1 Is2: ival A)
      (Ic: ival_couplingP Is1 Is2 (λ x y, x = y)): eq_ival Is1 Is2.
Proof.
  destruct Ic as [Ic Hp1 Hp2].
  setoid_rewrite Hp1. setoid_rewrite Hp2.
  apply ival_bind_congr; first by reflexivity.
  intros ((x&y)&Heq) => //=. rewrite //= in Heq; subst; reflexivity.
Qed.

Lemma ival_coupling_bind {A1 A2 B1 B2} (f1: A1 → ival B1) (f2: A2 → ival B2)
      Is1 Is2 P Q (Ic: ival_couplingP Is1 Is2 P):
  (∀ x y, P x y → ival_couplingP (f1 x) (f2 y) Q) →
  ival_couplingP (mbind f1 Is1) (mbind f2 Is2) Q.
Proof.
  intros Hfc.
  destruct Ic as [Ic Hp1 Hp2].
  unshelve (eexists).
  { refine (xy ← Ic; _). destruct xy as ((x&y)&HP).
    exact (Hfc _ _ HP).
  }
  - setoid_rewrite Hp1; setoid_rewrite ival_assoc;
      apply ival_bind_congr; first by reflexivity.
    intros ((x&y)&HP). setoid_rewrite ival_left_id => //=.
    destruct (Hfc x y); auto.
  - setoid_rewrite Hp2; setoid_rewrite ival_assoc;
      apply ival_bind_congr; first by reflexivity.
    intros ((x&y)&HP). setoid_rewrite ival_left_id => //=.
    destruct (Hfc x y); auto.
Qed.

Lemma ival_coupling_mret {A1 A2} x y (P: A1 → A2 → Prop):
  P x y →
  ival_couplingP (mret x) (mret y) P.
Proof.
  intros HP. exists (mret (exist _ (x, y) HP)); setoid_rewrite ival_left_id => //=; reflexivity.
Qed.

Lemma ival_coupling_conseq {A1 A2} (P1 P2: A1 → A2 → Prop) (I1: ival A1) (I2: ival A2):
  (∀ x y, P1 x y → P2 x y) →
  ival_couplingP I1 I2 P1 →
  ival_couplingP I1 I2 P2.
Proof.
  intros HP [Ic Hp1 Hp2].
  unshelve (eexists).
  { refine (x ← Ic; mret _).
    destruct x as (x&P).
    exists x. auto. }
  - setoid_rewrite Hp1.
    setoid_rewrite ival_assoc.
    eapply ival_bind_congr; first reflexivity; intros (?&?).
    setoid_rewrite ival_left_id; reflexivity.
  - setoid_rewrite Hp2.
    setoid_rewrite ival_assoc.
    eapply ival_bind_congr; first reflexivity; intros (?&?).
    setoid_rewrite ival_left_id; reflexivity.
Qed.

Lemma ival_coupling_plus' {A1 A2} p
      (P : A1 → A2 → Prop) (I1 I1': ival A1) (I2 I2': ival A2) :
  ival_couplingP I1 I2 P →
  ival_couplingP I1' I2' P →
  ival_couplingP (iplus (iscale p I1) (iscale (1 - p) I1'))
    (iplus (iscale p I2) (iscale (1 - p) I2')) P.
Proof.
  intros [Ic Hp1 Hp2] [Ic' Hp1' Hp2']. 
  exists (ival.iplus (ival.iscale p Ic) (ival.iscale (1 - p) Ic')). 
  - setoid_rewrite ival.ival_plus_bind.
    setoid_rewrite ival.ival_scale_bind.
    setoid_rewrite Hp1.
    setoid_rewrite Hp1'.
    reflexivity.
  - setoid_rewrite ival.ival_plus_bind.
    setoid_rewrite ival.ival_scale_bind.
    setoid_rewrite Hp2.
    setoid_rewrite Hp2'.
    reflexivity.
Qed.

Lemma ival_coupling_plus {A1 A2} p Hpf Hpf'
      (P : A1 → A2 → Prop) (I1 I1': ivdist A1) (I2 I2': ivdist A2) :
  ival_couplingP I1 I2 P →
  ival_couplingP I1' I2' P →
  ival_couplingP (ivdplus p Hpf I1 I1') (ivdplus p Hpf' I2 I2') P.
Proof.
  rewrite //=. apply ival_coupling_plus'.
Qed.

Lemma ival_coupling_idxOf {A1 A2} I1 I2 (P: A1 → A2 → Prop):
  ival_couplingP I1 I2 P →
  { Q :  {Q: idx I1 → idx I2 → Prop | (∀ i1 i1' i2, Q i1 i2 → Q i1' i2 → i1 = i1')} &
  ival_couplingP (idxOf I1) (idxOf I2) (λ i1 i2, P (ind I1 i1) (ind I2 i2) ∧
                                                 val I1 i1 > 0 ∧ val I2 i2 > 0 ∧
                                                 (sval Q) i1 i2  )}.
Proof.
  intros [Ic Hp1 Hp2].
  symmetry in Hp1. symmetry in Hp2.
  apply ClassicalEpsilon.constructive_indefinite_description in Hp1.
  destruct Hp1 as (h1&Hp1).
  apply ClassicalEpsilon.constructive_indefinite_description in Hp1.
  destruct Hp1 as (h1'&Hp1).
  apply ClassicalEpsilon.constructive_indefinite_description in Hp2.
  destruct Hp2 as (h2&Hp2).
  apply ClassicalEpsilon.constructive_indefinite_description in Hp2.
  destruct Hp2 as (h2'&Hp2).
  assert (Hgt_coerce: ∀ xy : support (val Ic),
             Rgt_dec (val Ic (projT1 (@existT _ (λ _, unit) (sval xy) tt)) * 1) 0).
  { abstract (intros (?&?); rewrite Rmult_1_r => //=; destruct Rgt_dec; auto). }
  unshelve (eexists).
  exists (λ i1 i2, ∃ ic1 ic2, sval (h1 ic1) = i1 ∧ sval (h2 ic2) = i2 ∧ sval ic1 = sval ic2).
  {
    abstract (intros i1 i1' i2 (ic1&ic2&Heq1&Heq2&Hcoh) (ic1'&ic2'&Heq1'&Heq2'&Hcoh');
    assert (ic2' = ic2);
    first ( abstract (destruct Hp2 as (Hbij2&?);
      rewrite -(Hbij2 ic2');
      rewrite -(Hbij2 ic2);
      f_equal; apply sval_inj_pred; congruence));
    abstract (subst; do 2 f_equal; apply sval_inj_pred; auto; congruence)). }
  unshelve (eexists).
  - refine (xy ← supp_idxOf Ic; mret _).
    unshelve (refine (exist _ ((sval (h1 _)), sval (h2 _)) _)).
      * exact (exist _ (existT (sval xy) tt) (Hgt_coerce xy)).
      * exact (exist _ (existT (sval xy) tt) (Hgt_coerce xy)).
      *
        abstract(
        split; [ by
        (abstract  (rewrite //=;
                   destruct Hp1 as (?&?&->&?) => //=;
                   destruct Hp2 as (?&?&->&?) => //=;
                   destruct (ind Ic (sval xy)) => //=)) |];
        split; [ by
        (abstract (rewrite //=; try destruct (h1 _); try destruct (h2 _); rewrite //=;
                   destruct Rgt_dec => //=)) |];
        split; [ by 
        (abstract (rewrite //=; try destruct (h1 _); try destruct (h2 _); rewrite //=;
                   destruct Rgt_dec => //=)) |];
        abstract (
        rewrite //=; 
        exists ((exist _ (existT (sval xy) tt) (Hgt_coerce xy)));
        exists ((exist _ (existT (sval xy) tt) (Hgt_coerce xy))); done)
        ).
  - setoid_rewrite ival_bind_mret_mret. 
    symmetry.
    unshelve (eexists).
    { 
      simpl. intros ((ic&?)&Hgt).
      simpl in h1.
      rewrite Rmult_1_r in Hgt.
      destruct ic as (ic&Hgtc).
      apply h1.
      exists (existT ic tt).
      simpl in *. rewrite Rmult_1_r. done.
    }
    unshelve (eexists).
    { simpl. intros ix.
      destruct (h1' ix) as ((i1&?)&Hgt).
      simpl in Hgt.
      unshelve (eexists).
      { unshelve (refine (existT _ tt)). 
        exists i1. rewrite Rmult_1_r in Hgt. done.
      }
      rewrite //=.
    }
    rewrite //=.
    repeat split.
    *  intros (((a&Hgt)&[])&?). destruct Hp1 as (Hinv1&Hinv1'&?).
      rewrite //=. destruct (Rmult_1_r _). rewrite /eq_rect_r //=.
      rewrite Hinv1 => //=.
      apply sval_inj_pred => //=.
      f_equal.
      apply sval_inj_pred => //=.
    * rewrite //= => a. destruct Hp1 as (Hinv1&Hinv1'&?).
      specialize (Hinv1' a).
      destruct (h1' a) as ((?&[])&?).
      rewrite //=.
      rewrite -Hinv1'. destruct (Rmult_1_r (val Ic x)) => //=.
    * rewrite //=. intros (((a&Hgt)&[])&?). destruct Hp1 as (Hinv1&Hinv1'&?).
      rewrite //=. destruct (Rmult_1_r _). rewrite /eq_rect_r //=.
      f_equal. f_equal.
      apply sval_inj_pred => //=.
    * rewrite //=. intros (((a&Hgt)&[])&?). destruct Hp1 as (Hinv1&Hinv1'&?&Hval).
      rewrite //=. destruct (Rmult_1_r _). rewrite /eq_rect_r //=.
      rewrite Hval //= !Rmult_1_r //.
  -  setoid_rewrite ival_bind_mret_mret. 
    symmetry.
    unshelve (eexists).
    { 
      simpl. intros ((ic&?)&Hgt).
      simpl in h1.
      rewrite Rmult_1_r in Hgt.
      destruct ic as (ic&Hgtc).
      apply h2.
      exists (existT ic tt).
      simpl in *. rewrite Rmult_1_r. done.
    }
    unshelve (eexists).
    { simpl. intros ix.
      destruct (h2' ix) as ((i1&?)&Hgt).
      simpl in Hgt.
      unshelve (eexists).
      { unshelve (refine (existT _ tt)). 
        exists i1. rewrite Rmult_1_r in Hgt. done.
      }
      rewrite //=.
    }
    rewrite //=.
    repeat split.
    * rewrite //=. intros (((a&Hgt)&[])&?). destruct Hp2 as (Hinv1&Hinv1'&?).
      rewrite //=. destruct (Rmult_1_r _). rewrite /eq_rect_r //=.
      rewrite Hinv1 => //=.
      apply sval_inj_pred => //=.
      f_equal.
      apply sval_inj_pred => //=.
    * rewrite //= => a. destruct Hp2 as (Hinv1&Hinv1'&?).
      specialize (Hinv1' a).
      destruct (h2' a) as ((?&[])&?).
      rewrite //=.
      rewrite -Hinv1'. destruct (Rmult_1_r (val Ic x)) => //=.
    * rewrite //=. intros (((a&Hgt)&[])&?). destruct Hp1 as (Hinv1&Hinv1'&?).
      rewrite //=. destruct (Rmult_1_r _). rewrite /eq_rect_r //=.
      f_equal. f_equal.
      apply sval_inj_pred => //=.
    * rewrite //=. intros (((a&Hgt)&[])&?). destruct Hp2 as (Hinv1&Hinv1'&?&Hval).
      rewrite //=. destruct (Rmult_1_r _). rewrite /eq_rect_r //=.
      rewrite Hval //= !Rmult_1_r //.
Qed.

Lemma ival_coupling_equip {X} I1 (P: X → Prop) Hpf:
  ival_couplingP I1 (ival_equip I1 P Hpf) (λ x y, x = (sval y)).
Proof.
  unshelve eexists.
  refine ((x ← ival_equip I1 P Hpf; mret (exist _ (sval x, x) _))); auto.
  - setoid_rewrite ival_bind_mret_mret. 
    rewrite /sval.
    etransitivity; first (symmetry; apply ival_right_id).
    apply ival_bind_P.
  - setoid_rewrite ival_bind_mret_mret. 
    rewrite /sval.
    etransitivity; first (symmetry; apply ival_right_id).
    eapply ival_bind_congr; first reflexivity.
    intros (?&?) => //=. reflexivity.
Qed.

Lemma ival_idist_wit_sum1 {X Y} (I1 : ivdist X) (I2: ivdist Y) (P: X → Y → Prop) Hwit:
  eq_ival I1 (Hwit ≫= (λ x : {xy : X * Y | P xy.1 xy.2}, mret (sval x).1)) →
  is_series (countable_sum (val Hwit)) 1.
Proof.
  intros Hproj1.
    eapply eq_ival_series in Hproj1; last apply (val_sum1).
    rewrite //= in Hproj1.
    setoid_rewrite Rmult_1_r in Hproj1.
    unshelve (eapply countable_series_rearrange_covering_match; last eapply Hproj1).
    { intros x. exists (existT (proj1_sig x) tt). exact (proj2_sig x). }
    { intros x; apply val_nonneg. }
    { intros x; apply val_nonneg. }
    { rewrite //=. intros (?&?) (?&?). inversion 1; subst. apply sval_inj_pi => //=. }
    { intros ((n&[])&Hpf). exists (exist _ n Hpf). apply sval_inj_pi => //=. }
    { intros (n&Hpf) => //=. }
Qed.

Lemma ival_idist_couplingP {X Y} (I1 : ivdist X) (I2: ivdist Y) (P: X → Y → Prop):
  ival_couplingP I1 I2 P →
  idist_couplingP I1 I2 P.
Proof.
  intros [Hwit Hproj1 Hproj2].
  unshelve (econstructor).
  { exists Hwit. eapply ival_idist_wit_sum1; eauto. }
  - rewrite /eq_ivd //=.
  - rewrite /eq_ivd //=.
Qed.

Lemma ival_coupling_support {X Y} I1 I2 (P: X → Y → Prop)
  (Ic: ival_couplingP I1 I2 P) : 
  ival_couplingP I1 I2 (λ x y, ∃ Hpf: P x y,  In_isupport x I1 ∧ In_isupport y I2 ∧
                        In_isupport (exist _ (x, y) Hpf) Ic).
Proof.
  destruct Ic as [Ic Hp1 Hp2].
  cut (ival_couplingP I1 I2 (λ x y, ∃ (Hpf: P x y), In_isupport (exist _ (x, y) Hpf) Ic)).
  { intros. eapply ival_coupling_conseq; last eauto. 
    intros x y (Hpf&Hin). 
    destruct Hin as (ic&Hind&Hval).
    exists Hpf.
    repeat split; auto.
      - rewrite //=. symmetry in Hp1.
        destruct Hp1 as (h1&?&?&?&Hind1&Hval1).
        unshelve (eexists). 
        { refine (sval (h1 _ )).
          exists (existT ic tt). rewrite //= Rmult_1_r. destruct Rgt_dec => //=.  }
        split; rewrite //=.
        * rewrite Hind1 //= Hind //=.
        * rewrite Hval1 //= Rmult_1_r //.
      - rewrite //=. symmetry in Hp2.
        destruct Hp2 as (h1&?&?&?&Hind1&Hval1).
        unshelve eexists.
        { refine (sval (h1 _)).
          exists (existT ic tt). rewrite //= Rmult_1_r. destruct Rgt_dec => //=.  }
        split; rewrite //=.
        * rewrite Hind1 //= Hind //=.
        * rewrite Hval1 //= Rmult_1_r //.
      - rewrite //=. exists ic; split => //=.
  }
  unshelve (eexists).
  refine (z ← ival_equip Ic (λ xy, In_isupport xy Ic) _; mret _).
  { destruct z as ((xy&HP)&Hin).  exists xy. abstract (exists HP; destruct xy; eauto). }
  { auto. }
  - setoid_rewrite Hp1.
    setoid_rewrite ival_bind_mret_mret.
    eapply ival_coupling_eq.
    eapply ival_coupling_bind; first eapply ival_coupling_equip.
    intros (xy&HP) ((xy'&HP')&Hin).
    rewrite //=. 
    inversion 1; subst; auto. apply ival_coupling_refl.
  - setoid_rewrite Hp2.
    setoid_rewrite ival_bind_mret_mret.
    eapply ival_coupling_eq.
    eapply ival_coupling_bind; first eapply ival_coupling_equip.
    intros (xy&HP) ((xy'&HP')&Hin).
    rewrite //=. 
    inversion 1; subst; auto. apply ival_coupling_refl.
Qed.

Lemma ival_coupling_support_wit {X Y} (I1: ivdist X) (I2: ivdist Y) (P: X → Y → Prop)
      (Ic: ival_couplingP I1 I2 P):
       { xy : X * Y | ∃ Hpf : P (fst xy) (snd xy),
           In_isupport (fst xy) I1 ∧ In_isupport (snd xy) I2 ∧ In_isupport (exist _ xy Hpf) Ic}.
Proof.
  specialize (ival_coupling_support I1 I2 P Ic) => Ic'.
  specialize (ival_idist_couplingP I1 I2 _ Ic') => Ic''. 
  destruct Ic'' as [Ic'' ? ?].
  destruct (ivd_support_idx Ic'') as (i&?).
  destruct (ind Ic'' i) as ((x&y)&?); eauto.
Qed.

Lemma ival_coupling_proper {X Y} I1 I1' I2 I2' (P: X → Y → Prop) :
  eq_ival I1 I1' → 
  eq_ival I2 I2' → 
  ival_couplingP I1 I2 P → 
  ival_couplingP I1' I2' P.
Proof.
  intros Heq1 Heq2 [Ic Hp1 Hp2].
  exists Ic; etransitivity; eauto; by symmetry.
Qed.
