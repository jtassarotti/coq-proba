From discprob.basic Require Import base order nify seq_ext.
From discprob.prob Require Import prob countable finite stochastic_order.
From discprob.monad Require Import monad monad_par_hoare monad_par par_quicksort par_quicksort_correct.
From discprob.monad Require  quicksort_cost.
From discprob.monad Require Import max_triangle.
From discprob.rec Require Import rec_convert quicksort_rec.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial finset.
From mathcomp Require Import path.
Require Import Reals Fourier Psatz Omega.

Definition h (l: seq nat) :=
  match l with
  | [::] => mret ([::], [::])
  | [::a] => mret ([::], [::])
  | a :: l => 
      p ← draw_pivot a l;
      spl ← dist_ret _ (partition' (sval p) (a :: l));
      mret (lower (sval spl), upper (sval spl))
  end.
Definition rsize (l: seq nat) := INR (size l).

Definition m x :=
  match (Rlt_dec x (4/3)) with
  | left _ => 0
  | _ => x * (3 / 4)
  end.

Lemma uniq_unif n:
  uniq (outcomes (unif n)).
Proof.
  rewrite /unif//=.
  rewrite map_inj_uniq.
  - apply enum_uniq.
  - intros (?&?) (?&?). inversion 1; auto.
    subst; f_equal. apply bool_irrelevance.
Qed.

Lemma uniq_unif2 n:
  uniq ([seq i.2 | i <- outcomes (unif n)]).
Proof.
  rewrite /unif//=.
  rewrite map_inj_in_uniq.
  - apply uniq_unif.
  - intros (?&?) (?&?).
    move /mapP => [? ? Heq1]. inversion Heq1; subst.
    move /mapP => [? ? Heq2]. inversion Heq2; subst.
    rewrite //=. inversion 1. repeat f_equal. 
    apply val_inj => //=.
Qed.

Lemma unif_all n x (Hle: (x <= n)%nat):
  {| work := O; span := O; result := exist _ x Hle|} \in [seq i.2 | i <- outcomes (unif n)].
Proof.
  apply /mapP.
  set (a := exist _ x Hle).
  replace {| work := 0; span := 0; result := a|} with 
          (1/INR (S n), {| work := 0; span :=0; result := a|}).2; last done.
  do 2 apply /mapP; eexists; eauto.
  rewrite /unif => //=.
  apply /mapP => //=.
  assert (Hlt: (x < S n)%nat) by auto.
  exists (Ordinal Hlt).
  - apply mem_enum. 
  - rewrite /a; repeat f_equal. apply bool_irrelevance.
Qed.

Lemma unif_all2 n x (Hle: (x <= n)%nat):
  exist _ x Hle \in [seq (result (i.2)) | i <- outcomes (unif n)].
Proof.
  apply /mapP.
  set (a := exist _ x Hle).
  replace a with 
          (result (1/INR (S n), {| work := 0; span :=0; result := a|}).2); last done.
  do 2 apply /mapP; eexists; eauto.
  rewrite /unif => //=.
  apply /mapP => //=.
  assert (Hlt: (x < S n)%nat) by auto.
  exists (Ordinal Hlt).
  - apply mem_enum. 
  - rewrite /a; repeat f_equal. apply bool_irrelevance.
Qed.

Lemma unif_cost n a w s : 
  {| work := w; span := s; result := a|} \in [seq i.2 | i <- outcomes (unif n)] → 
  w = O ∧ s = O.
Proof.
  replace {| work := w; span := s; result := a|} with
          (1/INR (S n), {| work := w; span := s; result := a|}).2; last done.
  move /mapP => [[r' [w' s' a']] Hin]. 
  move: Hin. rewrite /unif//=.
  move /mapP => [[w'' s'' a''] Hin] [] => ???. subst. inversion Hin. done.
Qed.

Lemma unif_cost2 n: 
  [seq {| work := O; span := O; result := result (i.2) |} | i <- unif n] = 
  [seq i.2 | i <- unif n].
Proof.  
  rewrite -eq_in_map.
  intros (r, a) Hin. 
  edestruct (unif_cost n (result a) (work a) (span a)) as [Heq1 Heq2].
  apply /mapP. exists (r, a); destruct a; eauto.
  destruct a as [w s a] => //=. rewrite //= in Heq1 Heq2. subst.
  done.
Qed.

Lemma unif_cost3 n: 
  [seq {| work := O; span := O; result := i|} 
  | i <- [seq result (i.2) | i <- unif n]] = [seq i.2 | i <- unif n].
Proof.  
  rewrite -map_comp -unif_cost2 => //=.
Qed.

Lemma unif_pr n a : 
  a \in [seq i.2 | i <- outcomes (unif n)] → 
  pr_eq (rvar_of_ldist (unif n)) a = 1 / INR (S n).
Proof.
  intros Hin. rewrite pr_rvar_ldist /unif//=.
  rewrite big_map -big_filter //=.
  destruct a as [w s (x&Hle)] => //=.
  assert (w = O ∧ s = O) as (?&?); last subst.
  { eapply unif_cost. apply Hin. }
  assert (Hlt: (x < S n)%nat) by auto.
  rewrite (bigD1_seq (Ordinal Hlt)) => //=.
  - rewrite -[a in _ = a]Rplus_0_r; f_equal.
    rewrite -big_filter -filter_predI big_filter. apply big_pred0.
    intros i => //=. apply negbTE. apply /andP => [] []. move /eqP => Heq.
    move /eqP => []. intros. subst. apply Heq.
    destruct i. f_equal. apply bool_irrelevance. 
  - rewrite mem_filter. apply /andP; split; auto. 
    * apply /eqP; f_equal; auto. f_equal. apply bool_irrelevance.
    * apply mem_enum. 
  - apply /filter_uniq/enum_uniq.
Qed.

Lemma partition_split l pv:
  let x := partition' pv l in
  lower (sval (result x)) = [ seq n <- l | ltn n pv] ∧
  middle (sval (result x)) = [ seq n <- l | n == pv] ∧
  upper (sval (result x)) = [ seq n <- l | ltn pv n].
Proof.
      induction l as [|a l]; first by rewrite //=.
      rewrite //=; case (ltngtP a pv) => //= ?;
      destruct (IHl) as (?&?&?); repeat split; auto; f_equal; done.
Qed.

Lemma Ex_max_partition_sum l: 
  Ex (rvar_comp (rvar_of_ldist (h l)) (λ x, Rmax (rsize (result x).1) (rsize (result x).2))) <=
  match (size l) with
     | O => 0
     | _ => \big[Rplus/0]_(i < size l) (/INR (size l) * (Rmax (INR i) (INR (size l - i - 1))))
  end.
Proof.
  destruct l as [| a l].
  - rewrite Ex_fin_comp.
    rewrite -(big_map _ (λ x, true) (λ a, pr_eq _ a * _ (_ (fst (result a))) (_ (snd (result a))))).
    rewrite img_rvar_of_ldist//=/img/undup//= !big_cons ?big_nil.
    rewrite pr_mret_simpl //= /m/rsize//=.
    rewrite Rmax_left //; last (fourier). 
    rewrite /INR. ring_simplify. fourier. 
  - destruct l as [| b0 l0].
    { 
      rewrite Ex_fin_comp. 
      rewrite -(big_map _ (λ x, true) (λ a, pr_eq _ a * _ (_ (fst (result a))) (_ (snd (result a))))).
      rewrite img_rvar_of_ldist//=/img/undup//= !big_cons ?big_nil.
      rewrite pr_mret_simpl //= /m/rsize//=.
      rewrite Rmax_left //; last (fourier). 
      replace (INR 0) with 0 by auto. ring_simplify. 
      apply Rle_big0 => i _ //=.
      destruct i as (i&Hlt) => //=. assert (i = O) as -> by (nify; omega). 
      replace (1 - 0 - 1)%nat with O by (nify; omega).
      replace (INR 0) with 0 by auto. rewrite Rmax_left; last fourier. 
      replace (INR 1) with 1 by auto. fourier.
    }
    remember (b0 :: l0) as l eqn:Heql0.

    replace (size (a :: l)) with (S (size l)) by auto. 
    rewrite -(Ex_mbind_mret (h (a :: l))).
    rewrite /h Heql0. rewrite -Heql0. clear l0 Heql0.

    rewrite ldist_assoc. rewrite ldist_assoc.
    rewrite Ex_mbind_ldist2.
    rewrite undup_id; last first.
    { apply uniq_unif2. } 
    rewrite -unif_cost3 big_map.
    edestruct (quicksort_cost.perm_eq_bij O) as (f&Hfspec&Hfsize&Hinv&Hinj).
    { rewrite perm_eq_sym. apply (perm_eqlE (perm_sort leq (a :: l))). }
    eapply sum_reidx_map_le with 
        (h := (λ (H : {x : nat | (x <= size l)%nat}), 
               let (x, i) := H in 
                (Ordinal (n:=(size l).+1) (m:=f x) (Hfsize x i)))).
    * intros (x, Hle) Hin. 
      rewrite unif_pr. rewrite /Rdiv Rmult_1_l. apply Rmult_le_compat_l. 
      ** left. apply Rinv_0_lt_compat. apply lt_0_INR. rewrite //=. omega. 
      ** rewrite -ldist_assoc. rewrite Ex_mbind_mret. 
         apply Ex_bound. 
         rewrite (ldist_cost_bind_fold (λ x, spl ← dist_ret _ (partition' (sval x) (a :: l));
                                             mret (lower (sval spl), upper (sval spl)))).
         rewrite ?ldist_left_id.
         assert (Hlt: (x < size (a :: l))%nat) by auto.
         rewrite //= in Hlt.
         eapply (@cspec_mspec _ _ (λ x0 : (seq nat * seq nat),
                                      Rmax (rsize x0.1) (rsize x0.2) 
                                      <= Rmax (INR (f (Ordinal (n:= S (size l)) Hle)))
                                              (INR (S (size l) - (f (Ordinal (n := S (size l)) Hle)) 
                                                    - 1)))).
         tbind (λ y, nth 0%nat (a :: l) x = sval y). 
         { apply mspec_mret => //=. }
         intros (pv&Hin') Heq.
         tbind (λ x, lower (sval x) = [ seq n <- (a :: l) | ltn n pv] ∧
                     middle (sval x) = [ seq n <- (a :: l) | n == pv] ∧
                     upper (sval x) = [ seq n <- (a :: l) | ltn pv n]).
         { apply mspec_mret. apply partition_split. }
         remember (a :: l) as l0 eqn:Heql0.
         assert (Hsize: S (size l) = (size l0)) by (rewrite Heql0; auto).
         intros (spl&Hin'') => //=. intros (Hl&Hm&Hu).
         apply mspec_mret => //=.
         rewrite /rsize. 
         rewrite !Rmax_INR. apply le_INR. 
         rewrite Hl Hu.
         apply Nat.max_le_compat.
         *** rewrite //= in Heq. rewrite -Heq. 
             apply /leP. rewrite Hfspec. 
             specialize (perm_eqlE (perm_sort leq l0)) => Hperm.
             rewrite -(perm_eq_size (quicksort_cost.perm_filter _ _ Hperm)).
             apply quicksort_cost.lower_split_size_sorted_nth; auto.
             **** apply sort_sorted => ??. apply leq_total.
             **** rewrite (perm_eq_size (perm_eqlE (perm_sort leq l0))) /=.
                  apply Hfsize. rewrite Heql0. done.
             **** rewrite Heql0 //=.
         *** rewrite //= in Heq. rewrite -Heq. 
             apply /leP. rewrite Hfspec. 
             assert (Hsize': (size l).+1 = size l0) by rewrite Heql0 //.
             rewrite Hsize'. 
             specialize (perm_eqlE (perm_sort leq l0)) => Hperm.
             rewrite -(perm_eq_size (perm_eqlE (perm_sort leq l0))).
             rewrite -(perm_eq_size (quicksort_cost.perm_filter _ _ Hperm)).
             apply quicksort_cost.upper_split_size_sorted_nth; auto.
             **** apply sort_sorted => ??. apply leq_total.
             **** rewrite (perm_eq_size (perm_eqlE (perm_sort leq l0))) /=. 
                  apply Hfsize. rewrite Heql0. done.
             **** rewrite Heql0 //=.
      ** rewrite -unif_cost3 //. apply /mapP. eexists; eauto.
    * intros (?&?) Hin; split; auto. 
      rewrite /index_enum. rewrite -enumT. rewrite mem_enum => //=.
    * intros b Hin _ Hfalse. contradiction Hfalse.
      destruct b as (m, Hle).
      destruct (Hinv m Hle) as (x'&Hle'&Heq).
      exists (exist _ x' Hle'); repeat split; auto.
      ** apply unif_all2.
      ** apply ord_inj => //=.
    * eapply map_uniq with (f := λ x, {| work := O; span := 0; result := x|}). 
      rewrite unif_cost3. eapply uniq_unif2. 
    * rewrite /index_enum. rewrite -enumT. apply enum_uniq.
    * intros (?&?) (?&?) _ => //=. inversion 1; subst. apply /val_inj/Hinj => //=.
Qed.

Lemma Ex_max_partition l: 
  Ex (rvar_comp (rvar_of_ldist (h l)) (λ x, Rmax (rsize (result x).1) (rsize (result x).2))) <=
   m (rsize l).
Proof.
  eapply Rle_trans; [ apply Ex_max_partition_sum | apply quicksort_cost.sum_le_m ].
Qed.

Definition T := λ x, rvar_comp (rvar_of_ldist (qs x)) (λ x, INR (span x)).
  Definition a x := 
    match Rle_dec x 1 with
      | left _ => 0
      | _ =>
        match Rlt_dec x 2 with
        | left _ => (x - 1)
        | _ => 1
        end
    end.
Definition h' x := rvar_comp (rvar_of_ldist (h x)) result.

Lemma Trec: 
    ∀ x r,  pr_eq (T x) r = 
            \big[Rplus/0]_(x' : imgT (h' x)) 
                        (pr_eq (h' x) (sval x') * 
                         pr_eq (rvar_comp (rvar_pair (T (fst (sval x'))) (T (snd (sval x'))))
                                         (fun xy => Rmax (fst xy) (snd xy))) (r - a (rsize x))).
Proof.
  intros ls r.
  induction ls as [| a0 ls].
  - rewrite /T. rewrite -pr_mbind_mret. 
    rewrite -(big_map _ (λ x, true) 
     (λ x',
     (pr_eq (h' [::]) x' *
      pr_eq (rvar_comp
               (rvar_pair
                  (rvar_comp (rvar_of_ldist (qs x'.1)) (λ x, INR (span x)))
                  (rvar_comp (rvar_of_ldist (qs x'.2)) (λ x, INR (span x))))
               (λ xy : prod_eqType R_eqType R_eqType, Rmax xy.1 xy.2)) (r - a (rsize [::]))))).
    rewrite img_rvar_comp map_comp.
    rewrite img_rvar_of_ldist /h. 
    rewrite big_cons big_nil Rplus_0_r.
    rewrite /a/rsize/size. 
    replace (INR 0) with 0 by auto.
    destruct (Rlt_dec); last nra.
    specialize (pr_rvar_ldist ((x ← qs [::]; mret (INR (span x))))) => -> //=.
    rewrite big_cons big_nil /=.
    rewrite /pr_eq; rewrite 2!pr_eq_alt_comp.
    destruct (Rle_dec); last nra.
    
    rewrite -(big_map _ (λ x, true) (λ v, if result v == _ then
                                            pr_eq _ v
                                          else
                                            0)).
    rewrite -(big_map _ (λ x, true) (λ v, if Rmax (fst v) (snd v) == r - 0 then
                                            pr_eq _ v
                                          else
                                            0)).
    rewrite (eq_big_perm _ (img_pair_rv _ _ _ _)).
    rewrite allpairs_comp.
    rewrite img_rvar_comp map_comp (map_comp span).
    specialize (img_rvar_of_ldist (qs [::])) => ->.
    specialize (img_rvar_of_ldist (h [::])) => ->.
    rewrite ?big_cons ?big_nil ?Rplus_0_r //= ?Rminus_0_r.
    rewrite Rmax_left; last reflexivity.
    case: ifP; last (intros; field).
    rewrite pr_mret_simpl //=. intros. ring_simplify. rewrite pr_eq_rvar_pair //=.
    rewrite /pr_eq pr_eq_alt_comp.
    rewrite -(big_map _ (λ x, true) (λ v, if INR (span (v)) == 0 then pr_eq _ v else 0)).
    rewrite -(big_map _ (λ x, true) (λ v, if INR (span (v)) == 0 then pr_eq _ v else 0)).
    specialize (img_rvar_of_ldist (qs [::])) => -> //=.
    rewrite ?big_cons ?big_nil //= eq_refl.
    rewrite pr_mret_simpl //=. field.
  - destruct ls as [| b0 ls0]. 
    { rewrite /T. rewrite -pr_mbind_mret. 
    rewrite -(big_map _ (λ x, true) 
     (λ x',
     (pr_eq (h' _) x' *
      pr_eq (rvar_comp
               (rvar_pair
                  (rvar_comp (rvar_of_ldist (qs x'.1)) (λ x, INR (span x)))
                  (rvar_comp (rvar_of_ldist (qs x'.2)) (λ x, INR (span x))))
               (λ xy : prod_eqType R_eqType R_eqType, Rmax xy.1 xy.2)) (r - a (rsize _))))).
    rewrite img_rvar_comp map_comp.
    rewrite img_rvar_of_ldist /h. 
    rewrite big_cons big_nil Rplus_0_r.
    rewrite /a/rsize/size. 
    replace (INR 1) with 1 by auto.
    destruct (Rlt_dec); last nra.
    specialize (pr_rvar_ldist ((x ← qs [:: a0]; mret (INR (span x))))) => -> //=.
    rewrite big_cons big_nil /=.
    rewrite /h'/h.
    rewrite {1}/pr_eq. rewrite 1!pr_eq_alt_comp.
    rewrite -(big_map _ (λ x, true) (λ v, if (result v) == _ then
                                            pr_eq _ v
                                          else
                                            0)).
    specialize (img_rvar_of_ldist (h [::a0])) => ->. rewrite /h.
    rewrite ?big_cons ?big_nil ?Rplus_0_r //= ?Rminus_0_r.
    rewrite pr_mret_simpl //=. ring_simplify. 
    rewrite {1}/pr_eq. rewrite 1!pr_eq_alt_comp.
    destruct (Rle_dec); last nra.
    rewrite /Rminus Ropp_0 Rplus_0_r.
    rewrite -(big_map _ (λ x, true) (λ v, if Rmax (fst v) (snd v) == r then
                                            pr_eq _ v
                                          else
                                            0)).
    rewrite (eq_big_perm _ (img_pair_rv _ _ _ _)). 
    rewrite allpairs_comp.
    rewrite img_rvar_comp map_comp (map_comp span).
    specialize (img_rvar_of_ldist (qs [::])) => -> //=.
    rewrite ?big_cons ?big_nil //=. replace (INR 0) with 0 by auto.
    rewrite ?Rplus_0_r.
    rewrite Rmax_left; last reflexivity.
    case: ifP; intros; last field.
    rewrite pr_eq_rvar_pair.
    f_equal.
    * rewrite /pr_eq pr_eq_alt_comp.
      rewrite -(big_map _ (λ x, true) (λ v, if INR (span (v)) == 0 then pr_eq _ v else 0)).
      specialize (img_rvar_of_ldist (qs [::])) => -> //=.
      rewrite ?big_cons ?big_nil //= eq_refl.
      rewrite pr_mret_simpl //=. field.
    * rewrite /pr_eq pr_eq_alt_comp.
      rewrite -(big_map _ (λ x, true) (λ v, if INR (span (v)) == 0 then pr_eq _ v else 0)).
      specialize (img_rvar_of_ldist (qs [::])) => -> //=.
      rewrite ?big_cons ?big_nil //= eq_refl.
      rewrite pr_mret_simpl //=. field.
    }
    remember (b0 :: ls0) as ls eqn:Heql0.
   rewrite /T. 
    rewrite qs_unfold.
    transitivity
  (pr_eq (rvar_comp (rvar_of_ldist
         ('(ll, lu) ← h (a0 :: ls);
            rpar2 (qs ll) (qs lu)
            )) (λ x, INR (span x)))  r); last first.
    {    
      rewrite /h'. 
    rewrite -(big_map _ (λ x, true) 
     (λ x',
     (pr_eq (h' _) x' *
      pr_eq (rvar_comp
               (rvar_pair
                  (rvar_comp (rvar_of_ldist (qs x'.1)) (λ x, INR (span x)))
                  (rvar_comp (rvar_of_ldist (qs x'.2)) (λ x, INR (span x))))
               (λ xy : prod_eqType R_eqType R_eqType, Rmax xy.1 xy.2)) (r - a (rsize _))))).

    rewrite img_rvar_comp map_comp.
    rewrite img_rvar_of_ldist.
    rewrite (cost_bind_const (3 * (size (a0 :: ls)))%nat (S O)).
      * rewrite -undup_map. rewrite -map_comp. 
        eapply eq_bigr. intros (ll&lu) _.
        f_equal. 
        specialize (ldist_cost_rpair_span (qs ll) (qs lu) 
                                    (λ x, INR (x + 1))) => ->.
        rewrite !rvar_pair_comp !rvar_comp_comp.
          rewrite {1}/pr_eq {1}[a in _ = a]/pr_eq.
          rewrite ?pr_eq_alt_comp /=. eapply eq_bigr => x ?.
          apply if_case_match. rewrite ?plus_INR ?Rmax_INR /rsize//=/a//=.
          rewrite Heql0 //=. specialize (S_INR (size ls0)) => /= => ->. 
          destruct (Rlt_dec).
          {specialize (pos_INR (size ls0)). intros. nra. } 
          destruct (Rle_dec); first nra.
          apply /eqP; apply /eqP. case: ifP; first by (move /eqP => ->; nra).
          move /eqP. intros. nra.
      * intros d'. rewrite map_comp. move /mapP. intros [? Hin Heq]. rewrite Heq. 
        cut (cspec (h (a0 :: ls )) (λ x, work x = 3 * size (a0 :: ls)))%nat; first by auto.
        rewrite /h. rewrite Heql0. rewrite -Heql0.
        cbind (λ x, work x = O). 
        { 
          rewrite /draw_pivot.
          cbind (λ x, work x = O).
          { rewrite /cspec/coutput. destruct y as [w s a].
            rewrite /work. eapply unif_cost; auto. }
          intros ? => /= ->.
          apply cspec_mret => //=.
        }
        intros pv ->.
        cbind (λ x, work x = 3 * size (a0 :: ls))%nat.
        { 
         eapply cspec_dist_ret.
         clear. rewrite /result. destruct pv as [w0 s0 (pv&?)]. rewrite /sval. 
         apply (partition_work (a0 :: ls) pv).
        }
        intros ? ->.
        apply cspec_mret => //=. nify. omega.
      (* Should re-work the lemma, because much of this is tedious and the same,
         it's just the final application of work/span of partition calculation *)
      * intros d'. rewrite map_comp. move /mapP. intros [? Hin Heq]. rewrite Heq. 
        cut (cspec (h (a0 :: ls )) (λ x, span x = 1))%nat; first by auto.
        rewrite /h. rewrite Heql0. rewrite -Heql0.
        cbind (λ x, span x = O). 
        { 
          rewrite /draw_pivot.
          cbind (λ x, span x = O).
          { rewrite /cspec/coutput. destruct y as [w s a].
            rewrite /work. eapply unif_cost; auto. }
          intros ? => /= ->.
          apply cspec_mret => //=.
        }
        intros pv ->.
        cbind (λ x, span x = 1)%nat.
        { 
         eapply cspec_dist_ret.
         clear. rewrite /result. destruct pv as [w0 s0 (pv&?)]. rewrite /sval. 
         apply (partition_span a0 ls pv).
        }
        intros ? ->.
        apply cspec_mret => //=.
    }
    (* TODO TODO: a good deal of this could be automated *) 
    rewrite Heql0.
    rewrite /h.
    rewrite -?pr_mbind_mret.
    f_equal.
    apply outcomes_eq_dist.
    rewrite ?ldist_assoc.
    f_equal; eapply ldist_bind_ext.
    intros ?. 
    eapply ldist_bind_ext.
    intros ?.
    rewrite ?ldist_assoc.
    eapply ldist_bind_ext.
    intros ?.
    rewrite ?ldist_assoc.
    rewrite ?ldist_left_id ?ldist_right_id.
    rewrite ?ldist_assoc.
    eapply ldist_bind_ext.
    intros ?.
    rewrite ?ldist_assoc.
    eapply ldist_bind_ext.
    intros ?. 
    rewrite ?ldist_left_id ?ldist_right_id.
    f_equal => //=. f_equal. nify. omega. 
Qed.

Definition k := -/ ln(3/4).

Theorem bound x w:
    rsize x > 1 →  
    pr_gt (T x) ((k * ln (rsize x) + 1) + INR w)
       ≤ (rsize x) * (3/4)^w.
Proof.
  specialize (quicksort_rec.recurrence_span2.qs_span_bound _ _ _ _ T h' (λ x, true)).
  rewrite /size/rsize => Hrec. eapply Hrec; clear; try done.
  - intros l ?. rewrite //=.
    rewrite /quicksort_rec.recurrence_span2.size //=.
    cut (∀ n, INR (length (fst (result (rvar_of_ldist (h l) n)))) + 
              INR (length (snd (result (rvar_of_ldist (h l) n)))) <=
                   INR (length l)); first by rewrite //=.
    intros n'. apply fun_to_cspec.
    rewrite /h.
    destruct l as [| a l].
    { apply cspec_mret => //=. replace (INR 0) with 0 by auto. nra. } 
    destruct l as [| b l0].
    { apply cspec_mret => //=. replace (INR 0) with 0 by auto. replace (INR 1) with 1 by auto. nra. } 
    remember (b::l0) as l eqn:Heql0.
    clear b l0 Heql0.
    eapply (cspec_mspec _ (λ x, INR (length (fst x)) + INR (length (snd x)) <= INR (length _))).
    tbind (λ x, sval x \in a :: l).
    { intros (?&?) => //. }
    intros (pv&Hin) _. 
    tbind (λ x, lower (sval x) = [ seq n <- (a :: l) | ltn n pv] ∧
                middle (sval x) = [ seq n <- (a :: l) | n == pv] ∧
                upper (sval x) = [ seq n <- (a :: l) | ltn pv n]).
    { remember (a :: l) as l0 eqn:Heql0.
      apply mspec_mret => //=. clear. induction l0 as [|a l]; first by rewrite //=.
      rewrite //=; case (ltngtP a pv) => //= ?;
      destruct (IHl) as (?&?&?); repeat split; auto; f_equal; done.
    }
    remember (a :: l) as l0 eqn:Heql0.
    intros (spl&Hin') => //= ?. apply mspec_mret.
    move /andP in Hin'.
    destruct Hin' as (pf1&pf2); move /implyP in pf2.
    replace (length l0) with (size l0) by auto.
    rewrite -(perm_eq_size pf1) //= ?size_cat -?plusE //.
    assert (Hlt: (lt O (size (middle spl)))) by
            ( apply /ltP; apply pf2 => //=; destruct p; eauto; subst; rewrite //=).
    rewrite -plus_INR. apply le_INR. rewrite //=.
    assert (length (lower spl) = size (lower spl)) as Heq by auto.
    rewrite Heq. clear Heq.
    assert (length (upper spl) = size (upper spl)) as Heq by auto.
    rewrite Heq. clear Heq.
    clear -Hlt. rewrite //=. omega. 
  - rewrite /quicksort_rec.recurrence_span2.size //=.
    intros l ? Hgt. rewrite //=.
    cut (∀ n, INR (length (fst (result (rvar_of_ldist (h l) n)))) + 
              INR (length (snd (result (rvar_of_ldist (h l) n)))) <=
                   INR (length l) - 1); first by rewrite //=.
    intros n'. apply fun_to_cspec.
    rewrite /h.
    destruct l as [| a l].
    { move : Hgt. rewrite //=. replace (INR 0) with 0 by auto. nra. } 
    destruct l as [| b l0].
    { move : Hgt. rewrite //=. replace (INR 1) with 1 by auto. nra. } 
    remember (b::l0) as l eqn:Heql0.
    clear b l0 Heql0.
    eapply (cspec_mspec _ (λ x, INR (length (fst x)) + INR (length (snd x)) <= INR (length _) - 1)).
    tbind (λ x, sval x \in a :: l).
    { intros (?&?) => //. }
    intros (pv&Hin) _. 
    tbind (λ x, lower (sval x) = [ seq n <- (a :: l) | ltn n pv] ∧
                middle (sval x) = [ seq n <- (a :: l) | n == pv] ∧
                upper (sval x) = [ seq n <- (a :: l) | ltn pv n]).
    { remember (a :: l) as l0 eqn:Heql0.
      apply mspec_mret => //=. clear. induction l0 as [|a l]; first by rewrite //=.
      rewrite //=; case (ltngtP a pv) => //= ?;
      destruct (IHl) as (?&?&?); repeat split; auto; f_equal; done.
    }
    remember (a :: l) as l0 eqn:Heql0.
    intros (spl&Hin') => //= ?. apply mspec_mret.
    move /andP in Hin'.
    destruct Hin' as (pf1&pf2); move /implyP in pf2.
    replace (length l0) with (size l0) by auto.
    rewrite -(perm_eq_size pf1) //= ?size_cat -?plusE //.
    assert (Hlt: (lt O (size (middle spl)))) by
            ( apply /ltP; apply pf2 => //=; destruct p; eauto; subst; rewrite //=).
    rewrite ?plus_INR.
    assert (length (lower spl) = size (lower spl)) as Heq by auto.
    rewrite Heq. clear Heq.
    assert (length (upper spl) = size (upper spl)) as Heq by auto.
    rewrite Heq. clear Heq.
    specialize (pos_INR (size (lower (spl)))).
    specialize (pos_INR (size (upper (spl)))).
    rewrite //=. intros.
    assert (Hge1: 1 <= INR (size (middle spl))).
    { replace 1 with (INR 1) by auto. apply le_INR. omega. } 
    rewrite //= in Hge1. nra.
  - rewrite /quicksort_rec.recurrence_span2.size/quicksort_rec.recurrence_span2.rec_solution.d //=.
    intros x n Hle.
    replace 1 with (INR 1) in Hle by auto. apply INR_le in Hle.
    cut (INR (span (rvar_of_ldist (qs x) n)) = 0); first by rewrite //=. 
    apply fun_to_cspec.
    destruct x; [| destruct x].
    * rewrite qs_unfold.
      apply cspec_mret => //=.
    * rewrite qs_unfold.
      apply cspec_mret => //=.
    * rewrite //= in Hle. omega.
  - intros. eapply (rec_pr_rec_gt _ rsize _ _ _ _ T h' (λ x, true) (λ xy, Rmax (fst xy) (snd xy)));
              auto; intros; apply Trec.
  - intros x. 
    rewrite /quicksort_rec.recurrence_span2.size/quicksort_rec.recurrence_span2.rec_solution.d
            /quicksort_rec.recurrence_span2.rec_solution.m
            /quicksort_rec.recurrence_span2.qs_factor.alpha.
    etransitivity; first eapply Ex_max_partition.
    rewrite /m/rsize/size/length. do 2 destruct Rlt_dec; try nra.
Qed.
