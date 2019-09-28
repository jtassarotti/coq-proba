From discprob.basic Require Import base Series_Ext seq_ext nify.
From discprob.prob Require Import countable rearrange prob.
Require Import Reals Fourier Omega Psatz.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice fintype bigop seq.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy Markov.

Definition finite_sum {A: finType} (f: A → R) :=
  λ n: nat, oapp f R0 (nth_error (Finite.enum A) n).

Section finite_sum_facts.

Variable (A: finType).
Implicit Types (a: A → R).

Lemma ex_series_eventually0 (a: nat → R):
  (∃ N, ∀ n, n ≥ N → a n = 0) → ex_series a.
Proof.
  intros (N&Hev0). apply: ex_series_Cauchy. 
  rewrite /Cauchy_series => eps. exists N => n m Hlen Hlem.
  assert (Heq: sum_n_m a n m = 0).
  { 
    rewrite /sum_n_m. 
    rewrite (Iter.iter_nat_ext_loc _ _ _ (λ x, 0)).
    - rewrite /plus/zero//=/Iter.iter_nat Iter.iter_const; nra.
    - intros k (?&?). apply Hev0. lia. 
  }
  rewrite /norm//=/abs//=. destruct eps =>//=. rewrite Heq Rabs_right; nra. 
Qed.

Lemma ex_series_list_Rabs {B: eqType} (l: list B) (f: B → R):
  ex_series (λ n, Rabs (oapp f R0 (nth_error l n))).
Proof.
  apply ex_series_eventually0.
  exists (length l) => n Hge.
  rewrite /finite_sum (proj2 (nth_error_None _ _)); last omega.
  rewrite Rabs_right => //=; nra.
Qed.

Lemma ex_seriesF_Rabs a:
  ex_series (λ n, Rabs (finite_sum a n)).
Proof.
  apply ex_series_list_Rabs.
Qed.

Lemma ex_seriesF a:
  ex_series (finite_sum a).
Proof.
  apply ex_series_Rabs, ex_seriesF_Rabs.
Qed.

Lemma SeriesF_big_op a:
  Series (finite_sum a) = \big[Rplus/0]_(i in A) (a i).
Proof.
  rewrite /finite_sum/index_enum.
  induction (Finite.enum A) => //=.
  - rewrite big_nil. apply is_series_unique, is_series_0 => n.
    destruct n; auto.
  - rewrite big_cons Series_incr_1 //=. 
    * rewrite IHl; f_equal.
    * apply ex_series_Rabs, ex_series_list_Rabs.
Qed.

Lemma SeriesF_is_seriesC a:
  is_series (countable_sum a) (Series (finite_sum a)).
Proof.
  edestruct (ex_seriesF_Rabs); eauto.
  edestruct (series_rearrange_covering (finite_sum a) 
                                       (λ n, match pickle_inv A n with
                                             | Some a => seq.index a (Finite.enum A) 
                                             | None => length (Finite.enum A)
                                             end)) as (?&Hconv); eauto.
  - intros n n'. rewrite /finite_sum => //=.
    case_eq (pickle_inv A n) => //=; last first.
    { rewrite (proj2 (nth_error_None _ _)); last by omega. rewrite //=. }
    intros s Hpickle1.
    case_eq (pickle_inv A n') => //=; last first.
    { intros ? ? Heq. exfalso.
      cut (length (Finite.enum A) < length (Finite.enum A))%nat;
                         first by (intros; nify; omega). 
      rewrite -{1}Heq. rewrite -size_legacy. apply SSR_leq. rewrite seq.index_mem.
      by rewrite -enumT mem_enum.
    }
    intros s' Hpickle2.
    intros Hneq0 Hidxeq.
    assert (s = s').
    { 
      rewrite -[a in a = _](@seq.nth_index _ s s (Finite.enum A)); 
        last by rewrite -enumT mem_enum. 
      rewrite -[a in _ = a](@seq.nth_index _ s s' (Finite.enum A)); 
        last by rewrite -enumT mem_enum. 
      auto.
    }
    subst. 
    transitivity (pickle s').
    * apply (f_equal (oapp (@pickle A) n)) in Hpickle1.
      rewrite //= pickle_invK in Hpickle1. 
      done.
    * apply (f_equal (oapp (@pickle A) n')) in Hpickle2.
      rewrite //= pickle_invK in Hpickle2.
      done.
  - rewrite /finite_sum => n.
    rewrite /oapp. 
    case_eq (nth_error (Finite.enum A) n).
    * intros s Heq Hneq0.
      exists (pickle s). rewrite pickleK_inv.
      assert (n < length (Finite.enum A))%nat.
      {  apply nth_error_Some. congruence. }
      eapply nth_error_nth2 with (d := s) in Heq.
      rewrite -Heq. apply seq.index_uniq.
      { nify. rewrite size_legacy. done. } 
      rewrite -enumT. apply enum_uniq.
    * rewrite //=. 
  - eapply is_series_ext; last apply Hconv.
    intros n. rewrite /finite_sum/countable_sum.
    destruct (pickle_inv A n) as [s|] => //=.
    * rewrite (nth_error_nth1 s); last first.
      { rewrite -size_legacy.
        apply SSR_leq. rewrite seq.index_mem. by rewrite -enumT mem_enum.
      }
      rewrite seq.nth_index; last by rewrite -enumT mem_enum.
      rewrite //=.
    * rewrite (proj2 (nth_error_None _ _)); last by omega. done. 
Qed.

Lemma SeriesC_SeriesF a:
  Series (countable_sum a) = Series (finite_sum a).
Proof. apply is_series_unique, SeriesF_is_seriesC. Qed.

Lemma SeriesC_fin_big a:
  Series (countable_sum a) = \big[Rplus/0]_(i in A) (a i).
Proof. by rewrite SeriesC_SeriesF SeriesF_big_op. Qed.

Lemma SeriesF_is_seriesC' a v:
    \big[Rplus/0]_(i in A) a i = v →
    is_series (countable_sum a) v.
Proof.
  intros <-. rewrite -SeriesC_fin_big //= SeriesC_SeriesF.
  apply SeriesF_is_seriesC.
Qed.

End finite_sum_facts.

Section img_fin.
Variable (A: finType) (B: eqType).
Definition img_fin_enum (f: A → B) : seq (imgT f).
  refine (undup [seq _ | i <- Finite.enum A]).
  rewrite //=. exists (f i). rewrite /img. apply /exCP; eauto.
Defined.

Lemma img_fin_enum_sval (f: A → B):
  map sval (img_fin_enum f) = undup [seq (f i) | i <- Finite.enum A].
Proof.
  rewrite /img_fin_enum //=. 
  induction (Finite.enum A) => //=.
  - case: ifP. 
    * case: ifP. 
      ** intros. eauto.
      ** intros Hnin Hin. exfalso.
         move /mapP in Hin. destruct Hin as [x Hin Hex]. 
         inversion Hex.
         move /negP in Hnin. apply Hnin.
         apply /mapP. eexists; eauto.
    * case: ifP.
      ** eauto. intros Hin Hnin. eauto. exfalso. 
         move /mapP in Hin. destruct Hin as [x Hin Hex]. 
         move /negP in Hnin. apply Hnin.
         apply /mapP. eexists; eauto.
         apply /eqP. rewrite -(inj_eq val_inj) => //=. apply /eqP. done.  
      ** intros. rewrite ?big_cons.
         rewrite //=. f_equal. eauto.
Qed.

Lemma img_fin_uniq (f: A → B) : uniq (img_fin_enum f).
Proof.
  rewrite /img_fin_enum. apply undup_uniq.
Qed.


(*
Lemma img_fin_mem f : ∀ x, x \in img f ↔ x \in img_fin_enum f.
Proof.
  split.
  - rewrite /img. move /exCP => [a Heq]. move /eqP in Heq. rewrite -Heq.
    rewrite /img_fin_enum mem_undup map_f // mem_enum //.
  - rewrite /img_fin_enum mem_undup. move /mapP => [? ? ?]. subst. 
    rewrite /img. apply /exCP; eauto.
Qed.
*)

Lemma img_fin_mem f x : x \in img_fin_enum f.
Proof.
  rewrite /img_fin_enum mem_undup. destruct x as (x&Heq) => //=.
  generalize (Heq). move /exCP in Heq. destruct Heq as (a&Heq) => ?. 
  apply /mapP. exists a.
  - rewrite -enumT mem_enum //.
  - move /eqP in Heq. subst. f_equal.
    apply bool_irrelevance.
Qed.

Definition img_finMixin (f: A → B) := 
  Eval hnf in @UniqFinMixin [countType of imgT f] (img_fin_enum f) (img_fin_uniq f) (img_fin_mem f).
Canonical img_finType (f: A → B) := 
  Eval hnf in FinType (imgT f) (img_finMixin f). 
End img_fin.

Lemma img_fin_enum_sval_comp {A: finType} {B C: eqType} (f: A → B) (g: B → C):
  map sval (img_fin_enum _ _ (g \o f)) = undup [seq (g (f i)) | i <- Finite.enum A].
Proof.
  rewrite /img_fin_enum. rewrite img_fin_enum_sval; done. 
Qed.

Lemma img_fin_big {A: finType} {B: eqType} (f: A → B) (F: B → R) P:
  \big[Rplus/0]_(i in img_finType A B f | P (sval i)) (F (sval i)) =
  \big[Rplus/0]_(i <- undup [seq (f i) | i <- Finite.enum A] | P i) (F i). 
Proof.
  rewrite /img_finType /index_enum.
  rewrite {1}[@Finite.enum]unlock //=. 
  rewrite /img_fin_enum /imgT/img//=/index_enum.
  rewrite -big_map. rewrite img_fin_enum_sval. done.
Qed.

Lemma img_fin_big' {A: finType} {B: eqType} (f: A → B) (F: B → R) P:
  \big[Rplus/0]_(i <- img_fin_enum A B f | P (sval i)) (F (sval i)) =
  \big[Rplus/0]_(i <- undup [seq (f i) | i <- Finite.enum A] | P i) (F i). 
Proof.
 intros. etransitivity; last apply img_fin_big.
 rewrite /index_enum. rewrite [@Finite.enum]unlock //=.
Qed.

  Lemma ex_Ex_fin {A: finType} {Ω: distrib A} (X: rrvar Ω):
    ex_Ex X.
  Proof.
    rewrite /ex_Ex. eexists. apply SeriesF_is_seriesC.
  Qed.

  Hint Resolve ex_Ex_fin.

Section Ex_fin_prop.
  Variable (A: finType).
  Variable (Ω: distrib A).

Lemma Ex_fin_pt  (X: rrvar Ω):
  Ex X = \big[Rplus/0]_(a in A) (X a * (rvar_dist X) a).
Proof.
  rewrite Ex_pt //. rewrite SeriesC_fin_big //.
Qed.


Lemma Ex_fin_comp {B: eqType} (X: rvar Ω B) (f: B → R):
  Ex (rvar_comp X f) = \big[Rplus/0]_(a : imgT X) (pr_eq X (sval a) * f (sval a)).
Proof. 
  rewrite Ex_comp_pt.Ex_comp. rewrite SeriesC_fin_big //. apply ex_Ex_fin.
Qed.

Lemma Ex_fin_comp_mono {B: eqType} (X: rvar Ω B) (f: B → R) (g: B → R):
    (∀ x, f x <= g x) →
    Ex (rvar_comp X f) <= Ex (rvar_comp X g).
Proof.
  intros Hle. rewrite ?Ex_fin_comp. apply Rle_bigr => a ?.
  apply Rmult_le_compat_l.
  * apply Rge_le, pr_eq_ge_0.
  * eauto.
Qed.

Lemma pr_sum_all {B: eqType} (X: rvar Ω B): 
  \big[Rplus/0]_(i : imgT X) pr_eq X (sval i) = 1.
Proof.
  transitivity (Ex (rvar_comp X (fun _ => 1))).
  - rewrite Ex_fin_comp. apply eq_bigr => ??. field. 
  - rewrite Ex_fin_pt //= -big_distrr //= Rmult_1_l -SeriesC_fin_big.
    apply is_series_unique, pmf_sum1.
Qed.

Lemma Ex_comp_ext {B: eqType} (X: rvar Ω B) (f f': B → R):
  (∀ x, f x = f' x) → 
  Ex (rvar_comp X f) = Ex (rvar_comp X f').
Proof.
  intros Hext. rewrite ?Ex_fin_pt.
  apply eq_bigr => ?? //=. by rewrite Hext.
Qed.

Lemma Ex_fin_plus_l (X: rrvar Ω) (x: R):
  Ex (rvar_comp X (Rplus x)) = x + Ex X.
Proof. by apply Ex_plus_l. Qed.

Lemma Ex_fin_plus_r (X: rrvar Ω) (x: R):
  Ex (rvar_comp X (λ y, y + x)) = Ex X + x.
Proof. by apply Ex_plus_r. Qed.

Lemma Ex_fin_scal_r (X: rrvar Ω) (c: R):
  Ex (rvar_comp X (λ x, x * c)) = Ex X * c.
Proof. by apply Ex_scal_r. Qed.

Lemma Ex_fin_scal_l (X: rrvar Ω) (c: R):
  Ex (rvar_comp X (λ x, c * x)) = c * Ex X.
Proof. by apply Ex_scal_l. Qed.

Lemma Ex_fin_sum (X Y: rrvar Ω):
  Ex (mkRvar Ω (λ x, X x + Y x)) =
  Ex X + Ex Y.
Proof. by apply Ex_sum. Qed.

Lemma img_rvar_comp {B B': eqType} (r: rvar Ω B) (f: B → B'):
  map sval (Finite.enum [finType of (imgT (rvar_comp r f))])
  = undup ([ seq (f (sval x)) | x <- Finite.enum [finType of (imgT r)]]).
Proof.
  rewrite /img//=. rewrite {1}unlock //=. rewrite img_fin_enum_sval_comp. 
  symmetry. rewrite {1}unlock //=. rewrite map_comp img_fin_enum_sval //=.
  rewrite -undup_map -map_comp. done.
Qed.
End Ex_fin_prop.


Arguments Ex_fin_pt {_ _}.
Arguments Ex_fin_comp {_ _ _}.
Arguments Ex_fin_comp_mono {_ _ _}.
Arguments pr_sum_all {_ _ _}.
Arguments Ex_comp_ext {_ _ _}.
Arguments Ex_fin_plus_l {_ _}.
Arguments Ex_fin_plus_r {_ _}.
Arguments Ex_fin_scal_l {_ _}.
Arguments Ex_fin_scal_r {_ _}.
Arguments Ex_fin_sum {_ _}.
Arguments img_rvar_comp {_ _ _ _}.

Lemma img_pair_rv {A A': finType} {B B': eqType} (Ω: distrib A) (Ω' : distrib A')
      (r: rvar Ω B) (r': rvar Ω' B'):
  perm_eq (map sval (Finite.enum [finType of imgT (rvar_pair r r')]))
          [seq (sval x1, sval x2) | x1 <- Finite.enum [finType of (imgT r)], 
                          x2 <- Finite.enum [finType of (imgT r')]].
Proof.
  rewrite /img/rvar_pair//= ?unlock /=/prod_enum ?enumT.
  apply uniq_perm_eq.
  - rewrite img_fin_enum_sval. apply undup_uniq.
  - apply allpairs_uniq; try (rewrite /img_fin_enum;  apply undup_uniq).
    intros x y ?? Heq => //=.
    destruct x as (s1&s1'), y as (s2&s2'). 
    f_equal. 
    * destruct s1, s2.  inversion Heq; subst. f_equal; apply bool_irrelevance.
    * destruct s1', s2'.  inversion Heq; subst. f_equal; apply bool_irrelevance.
  - intros (x, y). 
    apply /mapP. case: ifP => [HP|HnP].
    * move /allpairsP in HP. destruct HP as [(b&b') [Hb Hb' Heq]].
      rewrite mem_undup in Hb. move /mapP in Hb. destruct Hb as [a ? Hex].
      rewrite mem_undup in Hb'. move /mapP in Hb'. destruct Hb' as [a' ? Hex'].
      assert ((λ y, exC (λ x, (r (fst x), r' (snd x)) == y)) (x, y)) as Hpf.
      { 
        apply /exCP. exists (a, a').
        rewrite //= in Heq. inversion Heq. subst. 
        rewrite //= in Hex Hex'.
        apply /eqP; f_equal.
        - rewrite Hex => //=.
        - rewrite Hex' => //=.
      }
      exists (exist _ (x, y) Hpf).
      ** apply img_fin_mem.
      ** rewrite //=. 
    * intros [((b, b')&Hin0) Hin Heq]. 
      rewrite //= in Heq. move /negP in  HnP. apply HnP.
      apply /allpairsP. 
      rewrite //= in Hin.
      generalize (Hin0). move /exCP => [[a a'] Heq'].
      move /eqP in Heq'. inversion Heq'; subst.
      assert ((λ y, exC (λ x, r x == y)) x) as Hpfx.
      { apply /exCP. exists a. apply /eqP; inversion Heq; done. }
      assert ((λ y, exC (λ x, r' x == y)) y) as Hpfy.
      { apply /exCP. exists a'. apply /eqP; inversion Heq; done. }
      exists (exist _ x Hpfx, exist _ y Hpfy) => //=.
      split; try (apply img_fin_mem).
      done.
Qed.

Lemma Rmult_if_distrib (P : bool) v a b:
  (if P then a else b) * v =
  (if P then a * v else b * v).
Proof.
  destruct P => //=.
Qed.

Lemma pr_eq_rvar_pair {A A': finType} {B B': eqType} {Ω: distrib A} {Ω': distrib A'}
      (r: rvar Ω B) (r': rvar Ω' B') bb:
  pr_eq (rvar_pair r r') bb = pr_eq r (fst bb) * pr_eq r' (snd bb).
Proof.
  rewrite /pr_eq//=/pr ?SeriesC_fin_big.
  rewrite /index_enum -big_mkcondr.
  erewrite (eq_bigl (fun x => (r (fst x) == fst bb) && (r' (snd x) == (snd bb)))); last first. 
  { rewrite //= => x. }
  rewrite -(pair_big (λ x, r x == (fst bb)) (λ y, r' y == (snd bb)) 
                     (fun a b => rvar_dist r a * rvar_dist r' b)%R) //=.
  rewrite big_distrl /=.
  rewrite /index_enum.
  rewrite -big_mkcondr.
  transitivity 
    (\big[Rplus/0]_(i <- Finite.enum A | i \in A)
     ((if r i == bb.1 then (rvar_dist r) i *
      \big[Rplus_monoid/0]_(i0 <- Finite.enum A' | (i0 \in A') && (r' i0 == bb.2)) (rvar_dist r') i0
       else 0))); last first.
  { eapply eq_bigr => ??.  rewrite Rmult_if_distrib. case: ifP; auto. intros. field. }
  rewrite //=.
  rewrite -big_mkcondr.
  eapply eq_big.
  { intros x => //=. }
  intros a. move /eqP => Heq.
  rewrite -big_distrr /=.
  f_equal.
Qed.

Lemma rvar_pair_comp {A1 B1 A2 B2} {C1 C2: eqType} (Ω1: distrib A1) (Ω2: distrib A2)
      (r1: rvar Ω1 B1) (r2: rvar Ω2 B2) (f1: B1 → C1) (f2: B2 → C2):
  rvar_pair (rvar_comp r1 f1) (rvar_comp r2 f2) =
  rvar_comp (rvar_pair r1 r2) (λ xy, (f1 (fst xy), f2 (snd xy))).
Proof. by rewrite /=. Qed.