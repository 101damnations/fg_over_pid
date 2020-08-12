import tactic general set_lemmas linear_algebra.basis new_free ring_theory.principal_ideal_domain torsion primes
run_cmd tactic.skip
open_locale classical

variables {R : Type*} [integral_domain R] [is_principal_ideal_ring R]

noncomputable def projection {ι : Type*} {M : Type*} [add_comm_group M] [module R M]
  (v : ι → M) (hv : is_basis R v) (a : ι) :
  linear_map R M M :=
{ to_fun := λ x, x - hv.repr x a • v a,
  map_add' := λ x y, by {show (x + y) - hv.repr (x + y) a • v a = (x - _) + (y - _),
  rw linear_map.map_add, erw add_smul, abel, },
  map_smul' := λ c x, by {show c • x - hv.repr (c • x) a • v a = c • (x - _),
  rw linear_map.map_smul, rw smul_sub, rw ←mul_smul, refl, } }

theorem proj_mem {ι : Type*} {M : Type*} [add_comm_group M] [module R M]
  {s : set ι} {v : ι → M} (hv : is_basis R (v ∘ subtype.val : s → M)) {a : ι} (ha : a ∈ s) {x : M} :
  projection _ hv ⟨a, ha⟩ x ∈ submodule.span R (set.range (v ∘ subtype.val : (s \ {a} → M))) :=
begin
  show _ - _ ∈ _,
  conv {to_lhs, congr, rw ←hv.total_repr x},
  cases classical.em ((⟨a, ha⟩ : s) ∈ (hv.repr x).support),
  rw finsupp.total_apply, unfold finsupp.sum,
  rw ←finset.insert_erase h,
  erw finset.sum_insert (finset.not_mem_erase (⟨a, ha⟩ : s) (hv.repr x).support),
  simp only [add_sub_cancel', function.comp_app],
  refine @submodule.sum_mem R M _ _ _ _ (submodule.span R (set.range (v ∘ subtype.val))) (((hv.repr) x).support.erase ⟨a, ha⟩)
  (λ (y : s), ((hv.repr) x) y • v y.val) _,
  intros y hy, dsimp,
  apply submodule.smul_mem (submodule.span R (set.range (v ∘ subtype.val))) _,
  apply submodule.subset_span, use y,
  rw set.mem_diff, split,
  exact y.2,
  intro hya,
  have hyan : y = ⟨a, ha⟩ := subtype.ext_iff.2 hya,
  exact (finset.ne_of_mem_erase hy) hyan,
  rw finsupp.not_mem_support_iff.1 h, rw zero_smul, rw sub_zero,
    refine @submodule.sum_mem R M _ _ _ _ (submodule.span R (set.range (v ∘ subtype.val)))
      (((hv.repr) x).support)
  (λ (y : s), ((hv.repr) x) y • v y.val) _,
  intros y hy, dsimp,
  apply submodule.smul_mem (submodule.span R (set.range (v ∘ subtype.val))) _,
  apply submodule.subset_span, use y,
  rw set.mem_diff, split,
  exact y.2,
  intro hya,
  have hyan : y = ⟨a, ha⟩ := subtype.ext_iff.2 hya,
  rw hyan at hy, exact h hy,
end

lemma proj_ker {ι : Type*} {M : Type*} [add_comm_group M] [module R M]
  {s : set ι} {v : ι → M} (hv : is_basis R (v ∘ subtype.val : s → M)) {a : ι} (ha : a ∈ s) :
  (projection _ hv ⟨a, ha⟩).ker = submodule.span R {v a} :=
begin
  ext,
  split,
  intro hx,
  rw linear_map.mem_ker at hx,
  erw sub_eq_zero at hx,
  rw submodule.mem_span_singleton,
  use hv.repr x ⟨a, ha⟩,
  exact hx.symm,
  intro hx,
  rw submodule.mem_span_singleton at hx,
  cases hx with r hr,
  rw linear_map.mem_ker,
  erw sub_eq_zero,
  rw ←hr, rw linear_map.map_smul,
  have := @is_basis.repr_eq_single _ _ _ _ _ _ _ hv ⟨a, ha⟩,
  have hh : hv.repr ((v ∘ subtype.val) (⟨a, ha⟩ : s)) (⟨a, ha⟩ : s) = (1 : R) := by
    rw this; exact finsupp.single_eq_same,
  simp only [finsupp.smul_apply, algebra.id.smul_eq_mul, function.comp_app],
  rw mul_comm,
  rw mul_smul,
  rw hh, rw one_smul,
end

lemma projective_of_has_basis {ι : Type*} {M : Type*} [add_comm_group M] [module R M]
  {v : ι → M} (hv : is_basis R v) :
  projective R M :=
begin
  intros _ _ _ _ _ _ _ _ hg,
  let F' := λ i : ι, classical.some (hg (f (v i))),
  let F := @is_basis.constr _ _ _ _ _ _ _ _inst_6 _ _inst_7 hv F',
  use F,
  have huh : ∀ i : ι, g (F $ v i) = f (v i) := by {
  intro i, rw constr_basis, exact classical.some_spec (hg (f $ v i))},
  have : @linear_map.comp R M A B _ _ (@add_comm_group.to_add_comm_monoid A _inst_6)
   (@add_comm_group.to_add_comm_monoid B _inst_7_1) _ _ _ g F = f := @is_basis.ext
     _ _ _ _ _ _ _ _inst_7_1 _ _inst_7_2 (@linear_map.comp R M A B _ _
     (@add_comm_group.to_add_comm_monoid A _inst_6) (@add_comm_group.to_add_comm_monoid B _inst_7_1)
     _ _ _ g F) f
    hv (λ x, huh x),
  intro x,
  rw ←this,
  refl,
end

lemma split_of_left_inv {M : Type*} [add_comm_group M] [module R M] (A : submodule R M)
{B : Type*} [add_comm_group B] [module R B] (f : M →ₗ[R] B) (H : A.subtype.range = f.ker)
(g : B →ₗ[R] M) (hfg : f.comp g = linear_map.id) (hf : f.range = ⊤) :
  A ⊓ g.range = ⊥ ∧ A ⊔ g.range = ⊤ :=
begin
  split,
  rw eq_bot_iff,
  intros x hx,
  refine (submodule.mem_bot R).2 _,
  cases hx.2 with y hy,
  have : f x = 0, by {rw ←linear_map.mem_ker, rw ←H, exact ⟨⟨x, hx.1⟩, trivial, rfl⟩},
  rw ←hy.2 at this, rw ←linear_map.comp_apply at this,
  rw hfg at this,
  rw linear_map.id_apply at this,
  rw ←hy.2,
  rw this,
  rw g.map_zero,
  rw eq_top_iff,
  intros x _,
  apply submodule.mem_sup.2,
  clear a,
  use x - g (f x),
  split,
  rw ←submodule.range_subtype A, rw H,
  rw linear_map.mem_ker,
  rw linear_map.map_sub,
  show f x - f.comp g (f x) = 0,
  rw hfg,
  exact sub_self (f x),
  use g (f x),
  split,
  exact linear_map.mem_range.2 ⟨f x, rfl⟩,
  rw sub_add_cancel,
end

variables {ι : Type*} {M : Type*} (s : set ι)
  [fintype ι] [add_comm_group M]
  [module R M] (v : ι → M)
  (a : ι)

variables (R)

def wtf' (i : (s \ ({a} : set ι) : set ι)) : submodule.span R
  (set.range (v ∘ subtype.val : s \ {a} → M)) :=
subtype.mk ((v ∘ subtype.val) i) (submodule.subset_span $ set.mem_range_self i)

variables {R}
lemma is_basis_diff {n : ℕ} {ι : Type*} {M : Type*} {s : set ι}
  [fintype ι] (hs : fintype.card ↥s = nat.succ n) [add_comm_group M]
  [module R M] {v : ι → M} (hv : is_basis R (v ∘ subtype.val : s → M))
  {a : ι} (ha : a ∈ s) :
 is_basis R (wtf' R s v a ∘ (subtype.val : (@set.univ (s \ ({a} : set ι) : set ι) : set _) →
   (s \ ({a} : set ι) : set ι))) :=
begin
  split,
  refine linear_independent.comp _ subtype.val subtype.val_injective,
  apply linear_independent_span,
  dsimp,
  cases hv with hv1 hv2,
  have := linear_independent.to_subtype_range hv1,
  have H := linear_independent.mono (show (set.range (v ∘ subtype.val : s \ {a} → M) ⊆
  set.range (v ∘ subtype.val : s → M)), by
  {rw set.range_subset_iff, intro y,
  exact ⟨⟨(y : ι), set.diff_subset _ _ y.2⟩, rfl⟩}) this,
  refine linear_independent.of_subtype_range _ H,
  have hi := linear_independent.injective hv1,
  intros x y h,
  have hxy : (⟨(x : ι), set.diff_subset _ _ x.2⟩ : s) = (⟨(y : ι), set.diff_subset _ _ y.2⟩ : s) :=
  hi (by simpa only [function.comp_app] using h),
  apply subtype.ext_iff.2, simpa only [] using hxy,
  refine linear_map.map_injective (submodule.ker_subtype _) _,
  rw submodule.map_subtype_top, rw ←submodule.span_image,
  rw ←set.range_comp, congr' 1,
  ext,
  split,
  rintro ⟨y, hy⟩, simp only [submodule.subtype_apply, function.comp_app, wtf'] at hy,
  rw ←hy, use y.1, refl,
  rintro ⟨y, hy⟩,
  rw ←hy, use y, simp only [wtf', submodule.subtype_apply, submodule.coe_mk, function.comp_app],
end

theorem free_subm0 (ι : Type*) [fintype ι] (s : set ι) (hs : fintype.card s = 0)
  (M : Type*) [add_comm_group M] [module R M] (v : ι → M)
  (hv : is_basis R (v ∘ (subtype.val : s → ι)))
  (S : submodule R M) : ∃ (t : set M), linear_independent R (λ x, x : t → M) ∧
    submodule.span R (set.range (λ x, x : t → M)) = S :=
begin
  use ∅,
  split,
  exact linear_independent_empty R M,
  cases hv with hv1 hv2,
  have hs := fintype.card_eq_zero_iff.1 hs,
  erw subtype.range_coe_subtype, erw submodule.span_empty,
  suffices : ∀ x : M, x = 0, by {symmetry, rw eq_bot_iff, intros x hx, apply (submodule.mem_bot R).2,
    exact this (x : M)},
  intro x,
  have : set.range (v ∘ (subtype.val : s → ι )) = ∅ :=
  by {apply set.range_eq_empty.2, intro h, cases h with y hy, exact hs y },
  rw this at hv2, rw submodule.span_empty at hv2,
  apply (submodule.mem_bot R).1, rw hv2, exact submodule.mem_top,
end

noncomputable def free_equiv {ι : Type*} (x : ι)
  {M : Type*} [add_comm_group M] [module R M] {v : ι → M}
  (hv : is_basis R (v ∘ (subtype.val : ({x}: set ι) → ι))) :
  linear_equiv R R M :=
equiv_of_is_basis (@is_basis_singleton_one ({x} : set ι) R
  (set.unique_singleton x) _) hv (equiv.refl _)


lemma free_subm1 (ι : Type*) [fintype ι] (s : set ι) (hs : ¬ 1 < fintype.card s)
  (M : Type*) [add_comm_group M] [module R M] (v : ι → M) (hv : is_basis R (v ∘ (subtype.val : s → ι)))
  (S : submodule R M) : ∃ (t : set M), linear_independent R (λ x, x : t → M) ∧
    submodule.span R (set.range (λ x, x : t → M)) = S :=
begin
  cases classical.em (S = ⊥),
  use ∅, split, exact linear_independent_empty _ _, rw h, simp,
  have : fintype.card s = 0 ∨ fintype.card s = 1 := by omega,
  cases this with hl hr, exact free_subm0 ι s hl M v hv S,
  cases fintype.card_eq_one_iff.1 hr with y hy,
  have hrange : set.range (v ∘ subtype.val) = {(v ∘ subtype.val) y} := by {rw ←set.image_univ,
  convert set.image_singleton, symmetry, rw ←set.univ_subset_iff, intros t ht, exact hy t,},
  have hys : {(y : ι)} = s := by {ext a, split, intro ha, convert y.2, intro ha,
  exact subtype.ext_iff.1 (hy ⟨a, ha⟩)},
  let Smap := S.map (@free_equiv R _ _ ι (y : ι) M _ _ v (hys.symm ▸ hv)).symm.to_linear_map,
  cases submodule.is_principal.principal Smap with c hc,
  let C := @free_equiv R _ _ ι (y : ι) M _ _ v (hys.symm ▸ hv) c,
  use {C},
  have hCy : C ∈ submodule.span R {(v ∘ subtype.val) y} := by {rw ←hrange, rw hv.2,
  exact submodule.mem_top,},
  cases submodule.mem_span_singleton.1 hCy with r hr,
  have hCS : S = submodule.span R {C} := by {simp only [Smap, C] at hc ⊢, rw ←set.image_singleton,
    erw submodule.span_image,
   rw ←hc, rw ←submodule.map_comp, symmetry, convert submodule.map_id S, ext z,
   exact linear_equiv.apply_symm_apply (@free_equiv R _ _ ι (y : ι) M _ _ v (hys.symm ▸ hv)) z,},
  have hC0 : C ≠ 0 := λ hC0, by {rw hC0 at hCS, change S = submodule.span R (⊥ : submodule R M) at hCS,
    erw submodule.span_eq at hCS, exact h hCS},
  have hr0 : r ≠ 0 := λ hr0, by {rw hr0 at hr, rw zero_smul at hr, apply hC0, exact hr.symm},
  split,
  refine linear_independent.mono _ _, exact {r • v (y : ι)}, rw ←hr,
  rw set.singleton_subset_iff, exact set.mem_singleton _,
  have hry : {r • v (y : ι)} = set.range (λ m : s, r • (v ∘ subtype.val) m) :=
    by {rw ←set.image_univ, erw ←@set.image_singleton _ _ (λ m : s, r • (v ∘ subtype.val) m) y,
     congr, exact set.eq_univ_of_forall hy},
  rw hry,
  apply linear_independent.to_subtype_range, rw linear_independent_iff,
  have hv1 := linear_independent_iff.1 hv.1, intros l hl,
  let L : {x // x ∈ s} →₀ R := finsupp.map_range (λ m, r • m) (smul_zero r) l,
  have hvL := hv1 L (by {rw finsupp.total_apply at hl ⊢, unfold finsupp.sum,
    simp only [finsupp.map_range_apply],
  rw finset.sum_subset (finsupp.support_map_range), convert hl,dsimp,
    simp only [mul_comm r, mul_smul], refl,
  intros X hX hX0, have hm := finsupp.not_mem_support_iff.1 hX0,
  rw finsupp.map_range_apply at hm,rw hm, rw zero_smul,
  }),
  ext,
  rw finsupp.ext_iff at hvL, specialize hvL a,
  exact or.resolve_left (mul_eq_zero.1 hvL) hr0,
  convert hCS.symm,
  simp only [subtype.range_coe_subtype], refl,
end

lemma one_empty {n : ℕ} {ι : Type*} {M : Type*} {s : set ι} [hι : fintype ι]
  (hs : fintype.card ↥s = n.succ)
[add_comm_group M] [module R M] {v : ι → M} (hv : is_basis R (v ∘ subtype.val : s → M))
{S : submodule R M} (h1 : 1 < fintype.card ↥s) {b : ι} (hb : b ∈ s)
{t : set ↥(submodule.span R (set.range (v ∘ subtype.val : s \ {b} → M)))}
(ht : linear_independent R (λ (x : t), (↑x : submodule.span R (set.range
 (v ∘ subtype.val : s \ {b} → M)))) ∧ submodule.span R (set.range (λ (x : ↥t),
 (↑x : submodule.span R (set.range
 (v ∘ subtype.val : s \ {b} → M))))) =
      submodule.map
        (linear_map.cod_restrict (submodule.span R (set.range (v ∘ subtype.val)))
           (projection (v ∘ subtype.val) hv ⟨b, hb⟩)
           (λ c, proj_mem hv hb))
        S)
{l : set ↥((projection (v ∘ subtype.val) hv ⟨b, hb⟩).ker)}
(hl :
  linear_independent R (λ (x : ↥l), (↑x : (projection (v ∘ subtype.val) hv ⟨b, hb⟩).ker)) ∧
    submodule.span R (set.range (λ (x : ↥l), (↑x : (projection (v ∘ subtype.val) hv ⟨b, hb⟩).ker))) =
    ((submodule.of_le $ @inf_le_right _ _ S (projection _ hv ⟨b, hb⟩).ker).range))
(h : l = ∅) :
∃ (t : set M),
    linear_independent R (λ (x : ↥t), (↑x : M)) ∧ submodule.span R (set.range (λ (x : ↥t), ↑x)) = S :=
begin
  use (submodule.span R (set.range (v ∘ subtype.val : s \ {b} → M))).subtype '' t,
  split,
  apply linear_independent.image_subtype,
  exact ht.1,
  simp only [disjoint_bot_right, submodule.ker_subtype],
  simp only [submodule.subtype_apply, subtype.range_coe_subtype],
  show submodule.span R ((submodule.span R (set.range (v ∘ subtype.val))).subtype '' t) = S,
  rw submodule.span_image,
  apply le_antisymm,
  rw submodule.map_le_iff_le_comap,
  intros y hy,
  simp only [submodule.mem_comap, submodule.subtype_apply],
  sorry, sorry,
end

theorem free_subm (ι : Type*) [fintype ι] (s : set ι) (n : ℕ) (hs : fintype.card s = n)
  (M : Type*) [add_comm_group M] [module R M] (v : ι → M) (hv : is_basis R (v ∘ (subtype.val : s → ι)))
  (S : submodule R M) : ∃ (t : set M), linear_independent R (λ x, x : t → M) ∧ submodule.span R (set.range (λ x, x : t → M)) = S :=
begin
  unfreezingI {revert ι M s,
  induction n using nat.case_strong_induction_on with n hn},
  intros ι M s hι h0 inst inst' v hv S,
    exact @free_subm0 _ _ _ ι hι s h0 M inst inst' v hv S,
  intros ι M s hι hs _ _ v hv S,
  resetI,
  cases (classical.em (1 < fintype.card s)) with h1 h1,
  rcases fintype.card_pos_iff.1 (show 0 < fintype.card s, by omega) with ⟨b, hb⟩,
  rcases hn n (nat.le_refl n) (s \ ({b} : set ι) : set ι)
    (submodule.span R (set.range (v ∘ subtype.val : (s \ ({b} : set ι)) → M))) (set.univ)
  (by {
    apply (add_right_inj 1).1, rw add_comm 1 n, rw ←nat.succ_eq_add_one n, rw ← hs,
    erw univ_card'', rw add_comm,
    rw (card_insert' (s \ ({b} : set ι)) not_mem_diff_singleton).symm,
    congr, rw ←eq_insert_erase_of_mem s b hb, apply_instance, apply_instance})
    (λ i, ⟨v i, submodule.subset_span $ set.mem_range_self i⟩)
    (by convert is_basis_diff hs hv hb)
   (S.map $ (projection _ hv ⟨b, hb⟩).cod_restrict (submodule.span R (set.range
     (v ∘ subtype.val : (s \ ({b} : set ι)) → M)))
   (λ c, proj_mem hv hb)) with ⟨t, ht⟩,
  rcases hn 1 (by omega) ({b} : set ι) (projection _ hv ⟨b, hb⟩).ker set.univ sorry
    (λ x, ⟨v x, by {rw proj_ker,apply submodule.subset_span,convert set.mem_singleton _, exact x.2.symm}⟩)
  (by {split,
  suffices : linear_independent R (v ∘ subtype.val : ({b} : set ι) → M), by
    {  apply linear_independent.comp _ subtype.val subtype.val_injective,
       erw linear_independent_comp_subtype at this,
       rw linear_independent_iff,intros l hl,
       specialize this (finsupp.emb_domain (function.embedding.subtype ({b} : set ι)) l)
         (by {rw finsupp.mem_supported, rw finsupp.support_emb_domain,
         intros x hx, rcases finset.mem_map.1 hx with ⟨y, hym, hy⟩,
         rw ←hy, exact y.2}), rw finsupp.total_apply at hl,
      rw finsupp.total_emb_domain at this,rw finsupp.total_apply at this,
      simp only [function.comp_app] at this,
      change ((l.sum (λ (i : ({b} : set ι)) (c : R), c • v (↑i : ι)) = 0) →
  (finsupp.emb_domain (function.embedding.subtype ({b} : set ι)) l = 0)) at this,
     specialize this (by {rw subtype.ext_iff at hl,dsimp at hl,rw ←hl,
     show _ = submodule.subtype _ _,
     conv_rhs {rw ←finsupp.total_apply},
     rw linear_map.map_finsupp_total, rw finsupp.total_apply,
     apply finset.sum_congr rfl, intros x hx, simp only [submodule.subtype_apply, submodule.coe_mk,
     function.comp_app], }),
     rw finsupp.ext_iff at this,ext,specialize this a,erw finsupp.emb_domain_apply at this,
     rw this,simp only [finsupp.zero_apply], },
  have huh := linear_independent.to_subtype_range hv.1,
  have hm := linear_independent.mono (show set.range (v ∘ subtype.val : ({b} : set ι) → M) ⊆
    set.range (v ∘ subtype.val : s → M), by
  {rw set.range_subset_iff, intro y, use b, exact hb, rw ←subtype.eta y y.2, simp only
    [function.comp_app, subtype.eta],
  exact congr_arg v y.2.symm,
  }) huh,
  apply linear_independent.of_subtype_range, intros c d hcd,
  rw subtype.ext_iff, rw (show (c : ι) = b, from c.2), symmetry, exact d.2, exact hm,
  apply linear_map.map_injective (projection _ hv ⟨b, hb⟩).ker.ker_subtype,
  rw submodule.map_subtype_top, rw ←submodule.span_image, symmetry,
  convert proj_ker hv hb,
  rw ←set.range_comp,
  ext m,
  split,
  rintro ⟨k, hk⟩,
  rw ← hk, show _ = _, simpa only [] using congr_arg v k.1.2,
  intro hm, use b, exact set.mem_singleton _, rw (show _ = _, from hm), refl,
  })
  (submodule.of_le $ @inf_le_right _ _ S (projection _ hv ⟨b, hb⟩).ker).range with ⟨l, hl⟩,
  cases (classical.em (l = ∅)),
    exact one_empty hs hv h1 hb ht hl h,
  let V := (submodule.span R (set.range (v ∘ subtype.val : (s \ ({b} : set ι)) → M))).subtype '' t,
  let W := (projection (v ∘ subtype.val) hv ⟨b, hb⟩).ker.subtype '' l,
  use V ∪ W,
  refine union_is_basis_of_gen_compl S ((submodule.span R (set.range (v ∘ subtype.val :
    (s \ ({b} : set ι)) → M))).comap S.subtype) V (submodule.comap S.subtype $
    linear_map.ker (projection (v ∘ subtype.val) hv ⟨b, hb⟩)) W _ _ _ _ _ _,
  rw submodule.map_comap_subtype,
    sorry,
  rw submodule.map_comap_subtype, sorry,
  refine linear_independent.image_subtype _ _,
  exact ht.1, sorry,
  refine linear_independent.image_subtype _ _,
  exact hl.1, sorry,
  rw ←submodule.comap_inf,
  rw eq_bot_iff,
  intros x hx, rw submodule.mem_bot,
  cases hx with hxl hxr,
  simp at hxr,
  sorry,
  sorry,
  exact free_subm1 ι s h1 M v hv S,
end

lemma tf_iff {M : Type*} [add_comm_group M] [module R M] :
  tors R M = ⊥ ↔ ∀ (x : M) (r : R), r • x = 0 → r = 0 ∨ x = 0 :=
begin
  split,
  intro h,
  rw eq_bot_iff at h,
  intros x r hx,
  cases (classical.em (r = 0)),
  left, assumption,
  right,
  exact (submodule.mem_bot R).1 (h ⟨r, h_1, hx⟩),
  intros h,
  rw eq_bot_iff,
  intros x hx,
  cases hx with r hr,
  exact (submodule.mem_bot R).2 (or.resolve_left (h x r hr.2) hr.1)
end

theorem fg_quotient {M : Type*} [add_comm_group M] [module R M]
  (S : submodule R M) (Hfg : S.fg) (A : submodule R S) : (⊤ : submodule R A.quotient).fg :=
@is_noetherian.noetherian _ _ _ _ _
  (is_noetherian_of_quotient_of_noetherian R S A $ is_noetherian_of_fg_of_noetherian S Hfg) ⊤

lemma span_insert_zero_eq' {s : set M} :
  submodule.span R (insert (0 : M) s) = submodule.span R s :=
begin
  rw ←set.union_singleton,
  rw submodule.span_union,
  rw submodule.span_singleton_eq_bot.2 rfl,
  rw sup_bot_eq,
end

lemma card_pos_of_ne_bot {M : Type*} [add_comm_group M] [module R M] {s : finset M}
  {S : submodule R M} (h : S ≠ ⊥) (hs : submodule.span R (↑s : set M) = S) :
  0 < (s.erase 0).card :=
begin
  rw nat.pos_iff_ne_zero,
  intro h0,
  rw finset.card_eq_zero at h0,
  cases classical.em ((0 : M) ∈ s) with hl hr,
  rw ←finset.insert_erase hl at hs,
  rw insert_to_set' at hs,
  rw span_insert_zero_eq' at hs,
  rw h0 at hs, erw submodule.span_empty at hs, exact h hs.symm,
  rw finset.erase_eq_of_not_mem hr at h0,
  rw h0 at hs, erw submodule.span_empty at hs,
  exact h hs.symm,
end

lemma subset_singleton' {c : M} {l : finset M} (h : l ⊆ {c}) : l = ∅ ∨ l = {c} :=
begin
  cases (finset.eq_empty_or_nonempty l),
  left,
  exact h_1,
  right,
  erw finset.eq_singleton_iff_unique_mem,
  cases h_1 with w hw,
  have := finset.mem_singleton.1 (h hw),
  rw ←this,
  split,
  exact hw,
  intros x hx,
  rw this,
  exact finset.mem_singleton.1 (h hx),
end

lemma single_of_singleton_support {α : Type*} {l : α →₀ R} {x : α}
  (h : l.support = {x}) : l = finsupp.single x (l x) :=
begin
  ext,
  cases classical.em (a = x),
  rw h_1, simp only [finsupp.single_eq_same],
  rw finsupp.not_mem_support_iff.1 (by rw h; exact finset.not_mem_singleton.2 h_1),
  rw finsupp.single_eq_of_ne (ne.symm h_1),
end


def WHY (s : finset M) : set M := @has_lift.lift _ _ finset.has_lift s


noncomputable def finsupp_insert {s : finset M} {x : M} {l :  (set.insert x (WHY s)) →₀ R}
  (hx : x ∉ s) (hl : l.2 (⟨x, set.mem_insert x (WHY s)⟩ : set.insert x (WHY s)) = 0) :
  WHY s →₀ R :=
{ support := subtype_mk' (finset.image subtype.val l.support) (WHY s) (by {intros y hy,
erw finset.mem_image at hy, rcases hy with ⟨z, hzm, hz⟩, rw ←hz, exact
or.resolve_left z.2 (by {intro hzx, rw finsupp.mem_support_iff at hzm, apply hzm, rw ←hl,
  congr, rw subtype.ext_iff, exact hzx})}),
  to_fun := λ x, l ⟨x, set.subset_insert _ _ x.2⟩,
  mem_support_to_fun := λ y, by {split, intros h h0, erw finset.mem_image at h,
  rcases h with ⟨b, hmb, hb⟩, cases b with b1 b2, erw finset.mem_image at b2, rcases b2 with ⟨c, hmc, hc⟩,
  apply finsupp.mem_support_iff.1 hmc, rw ←subtype.eta c c.2, rw ←h0, congr' 1,
    rw subtype.mk_eq_mk, rw hc, rw ←hb, refl,
    intros h0, apply finset.mem_image.2, use (y : M), apply finset.mem_image.2,
    use ⟨y, set.subset_insert _ _ y.2⟩,
    split, exact finsupp.mem_support_iff.2 h0, refl,
    split, exact finset.mem_univ _, rw subtype.ext_iff, refl,} }

lemma finsupp_insert_apply {s : finset M} {x : M} {l :  (set.insert x (WHY s)) →₀ R}
  (hx : x ∉ s) (hl : l.2 (⟨x, set.mem_insert x (WHY s)⟩ : set.insert x (WHY s)) = 0)
  {y : M} (hy : y ∈ s) : finsupp_insert hx hl ⟨y, hy⟩ = l ⟨y, set.subset_insert _ _ hy⟩ :=
rfl



lemma finsupp_insert_total {s : finset M} {x : M} {l :  (set.insert x (WHY s)) →₀ R}
  (hx : x ∉ s) (hl : l.2 (⟨x, set.mem_insert x (WHY s)⟩ : set.insert x (WHY s)) = 0)
  : finsupp.total (WHY s) M R subtype.val (finsupp_insert hx hl) =
    finsupp.total (set.insert x (WHY s)) M R subtype.val l :=
begin
  rw finsupp.total_apply,
  rw finsupp.total_apply,
  unfold finsupp.sum,
  show (subtype_mk' _ _ _).sum (λ (z : WHY s), l ⟨z, set.subset_insert _ _ z.2⟩ • (z : M)) = _,
  sorry,
end

variables (ρ : finset M) (T : set M)

instance fucksake2 (s : finset M) : fintype (WHY s) :=
finset_coe.fintype s

noncomputable def dep_coeff_map {M : Type*} [add_comm_group M] [module R M] (s : finset M) (z : M)
(h : ¬(finsupp.total (set.insert z (WHY s)) M R subtype.val).ker = ⊥) :
  (finsupp.total (set.insert z (WHY s)) M R subtype.val).ker :=
@classical.some (finsupp.total (set.insert z (WHY s)) M R subtype.val).ker (λ f, f ≠ 0) (by {
  have h' : ¬(finsupp.total (set.insert z (WHY s)) M R subtype.val).ker ≤ ⊥, from λ h', h (eq_bot_iff.2 h'),
  rcases submodule.not_le_iff_exists.1 h' with ⟨y, hym, hy⟩, use y,exact hym,
  intro hy0, rw subtype.ext_iff at hy0,
exact hy hy0})

noncomputable def dep_coeff {M : Type*} [add_comm_group M] [module R M] (s : finset M) (z : M)
(h : ¬(finsupp.total (set.insert z (WHY s)) M R subtype.val).ker = ⊥) : R :=
dep_coeff_map s z h ⟨z, (set.mem_insert z _)⟩

theorem dep_coeff_spec {M : Type*} [add_comm_group M] [module R M] (s : finset M) (z : M)
  (h : ¬(finsupp.total (set.insert z (WHY s)) M R subtype.val).ker = ⊥) :
  dep_coeff_map s z h ≠ 0 :=
@classical.some_spec (finsupp.total (set.insert z (WHY s)) M R subtype.val).ker (λ f, f ≠ 0) (by {
  have h' : ¬(finsupp.total (set.insert z (WHY s)) M R subtype.val).ker ≤ ⊥,
    from λ h', h (eq_bot_iff.2 h'),
  rcases submodule.not_le_iff_exists.1 h' with ⟨y, hym, hy⟩, use y,
    exact hym, intro hy0, rw subtype.ext_iff at hy0,
exact hy hy0})

lemma prod_ne_zero {M : Type*} [add_comm_group M] [module R M] (Y s : finset M)
(h : ∀ z : M, z ∈ Y \ s → ¬(finsupp.total (set.insert (z : M) (WHY s)) M R subtype.val).ker = ⊥)
  (hli : (finsupp.total (WHY s) M R subtype.val).ker = ⊥) :
 finset.prod (finset.image (λ w : (WHY (Y \ s)), dep_coeff s (w : M) $ h w w.2)
 (@finset.univ (WHY (Y \ s)) _)) id ≠ 0 :=
begin
  intro hr0,
  have hr := finset_prod_eq_zero_iff.1 hr0,
  rw finset.mem_image at hr, rcases hr with ⟨x, hxm, hx⟩,
  rw eq_bot_iff at hli,
  have H := classical.not_not.2 hli,
  apply H,
  rw submodule.not_le_iff_exists,
  let F := @finsupp_insert R _ _ _ _ _ s x (dep_coeff_map s x (h x x.2)) (finset.mem_sdiff.1 x.2).2 hx,
  use F,
  split,
  rw linear_map.mem_ker,
  erw finsupp_insert_total (finset.mem_sdiff.1 x.2).2 hx,
  have huh := (dep_coeff_map s (x : M) (h x x.2)).2,
  rw linear_map.mem_ker at huh, exact huh,
  intro hF0,
  apply dep_coeff_spec s (x : M) (h x x.2),
  rw submodule.mem_bot at hF0,
  rw subtype.ext_iff,
  rw submodule.coe_zero,
  ext,
  cases (set.mem_insert_iff.1 a.2),
  rw finsupp.zero_apply, rw ←hx, congr, rw subtype.ext_iff, exact h_1,
  have huh := finsupp.ext_iff.1 hF0 ⟨a, h_1⟩,
  rw finsupp_insert_apply at huh,
  rw subtype.coe_eta at huh, rw huh, refl,
end

lemma prod_smul_mem {M : Type*} [add_comm_group M] [module R M] (Y s : finset M)
(h : ∀ z : M, z ∈ Y \ s → ¬(finsupp.total (set.insert (z : M) (WHY s)) M R subtype.val).ker = ⊥)
 (hli : (finsupp.total (WHY s) M R subtype.val).ker = ⊥)
 {y} (hy : y ∈ Y) :
 finset.prod (finset.image (λ w : (WHY (Y \ s)), dep_coeff s (w : M) $ h w w.2)
 (@finset.univ (WHY (Y \ s)) _)) id • y ∈ submodule.span R (↑s : set M) :=
begin
  sorry,
end

variables {r : R} (S : submodule R M)

noncomputable def r_equiv (htf : ∀ (x : S) (r : R), r • x = 0 → r = 0 ∨ x = 0) (r : R) (hr : r ≠ 0) :=
linear_equiv.of_injective ((r • linear_map.id).comp S.subtype) (by {
rw linear_map.ker_eq_bot', intros m hm, exact or.resolve_left
(htf m r $ subtype.ext_iff.2 $ by {dsimp at hm, rw ←submodule.coe_smul at hm,
  rw ←@submodule.coe_zero _ _ _ _ _ S at hm, exact hm}) hr})

lemma equiv_apply (htf : ∀ (x : S) (r : R), r • x = 0 → r = 0 ∨ x = 0) (r : R) (hr : r ≠ 0) {x : S} :
(r_equiv S htf r hr x : M) = r • x := rfl

theorem free_of_tf (M : Type*) [add_comm_group M] [module R M] (S : submodule R M)
  (hfg : S.fg) (htf : ∀ (x : S) (r : R), r • x = 0 → r = 0 ∨ x = 0) :
  ∃ (t : set M), linear_independent R (λ x, x : t → M) ∧
  submodule.span R (set.range (λ x, x : t → M)) = S :=
begin
  cases (classical.em (S = ⊥)),
  {  use ∅,
       split,
       exact linear_independent_empty _ _,
       rw h, simp only [subtype.range_coe_subtype], exact submodule.span_empty},
  cases hfg with X hX,
  set Y := X.erase 0,
  have hY : (↑Y : set M) ⊆ S := set.subset.trans (finset.erase_subset 0 X) (hX ▸ submodule.subset_span),
  set n := nat.find_greatest (λ n, ∃ s : finset M, s ⊆ Y ∧
    linear_independent R (λ x, x : (WHY s) → M) ∧ s.card = n) Y.card,
  cases @nat.find_greatest_spec (λ n, ∃ s : finset M, s ⊆ Y ∧
    linear_independent R (λ x, x : (WHY s) → M) ∧ s.card = n) _ Y.card
    ⟨1, nat.succ_le_of_lt $ card_pos_of_ne_bot h hX, by
    {cases finset.card_pos.1 (card_pos_of_ne_bot h hX) with c hc,
    use {c}, split,
    exact finset.singleton_subset_iff.2 hc, split,
    rw linear_independent_subtype, intros l hlm hl,
    cases subset_singleton ((finsupp.mem_supported _ _).1 hlm) with hl0 hlc,
    rw ←finsupp.support_eq_empty, exact hl0,
    rw single_of_singleton_support hlc at hl ⊢,
    rw finsupp.total_single at hl,
    rw finsupp.single_eq_zero,
    exact or.resolve_right (htf ⟨c, hY hc⟩ (l c) (subtype.ext_iff.2 $ hl))
    (λ h0, (finset.mem_erase.1 hc).1 $ subtype.ext_iff.1 h0),
    exact finset.card_singleton _,
     }⟩ with s hs,
  cases (classical.em (∃ x, x ∈ Y \ s)),
  cases h_1 with z hz,
  have hnl : ∀ z, z ∈ Y \ s → ¬(linear_independent R $ (λ y, y : (set.insert z (WHY s) : set M) → M)) :=
    λ x hx hnl,
  by {have huh := @nat.find_greatest_is_greatest (λ n, ∃ s : finset M, s ⊆ Y ∧
    linear_independent R (λ x, x : (WHY s) → M) ∧ s.card = n) _ Y.card
      ⟨1, nat.succ_le_of_lt $ card_pos_of_ne_bot h hX, by
    {cases finset.card_pos.1 (card_pos_of_ne_bot h hX) with c hc,
    use {c}, split,
    exact finset.singleton_subset_iff.2 hc, split,
    rw linear_independent_subtype, intros l hlm hl,
    cases subset_singleton ((finsupp.mem_supported _ _).1 hlm) with hl0 hlc,
    rw ←finsupp.support_eq_empty, exact hl0,
    rw single_of_singleton_support hlc at hl ⊢,
    rw finsupp.total_single at hl,
    rw finsupp.single_eq_zero,
    exact or.resolve_right (htf ⟨c, hY hc⟩ (l c) (subtype.ext_iff.2 $ hl))
      (λ h0, (finset.mem_erase.1 hc).1 $ subtype.ext_iff.1 h0),
    exact finset.card_singleton _,
     }⟩ n.succ (by {split, exact nat.lt_succ_self _, rw nat.succ_le_iff, simp only [n], erw ←hs.2.2,
     apply finset.card_lt_card, rw finset.ssubset_iff_of_subset, use x,
     rw ←finset.mem_sdiff, exact hx, exact hs.1}),
     exact huh ⟨(insert x s), by {split, rw finset.insert_subset,split,
     exact (finset.mem_sdiff.1 hx).1, exact hs.1, split,
     simp only [*, not_exists, set.diff_singleton_subset_iff, submodule.mem_coe,
     finset.coe_erase, not_and, finset.mem_sdiff, ne.def,
   set.insert_eq_of_mem, submodule.zero_mem, finset.mem_erase] at *, convert hnl,
   all_goals {try {exact finset.coe_insert _ _}},
     rw finset.card_insert_of_not_mem, rw hs.2.2, exact (finset.mem_sdiff.1 hx).2,
      }⟩, },
  unfold linear_independent at hnl,
set r : R := finset.prod (finset.image (λ w : (↑(Y \ s) : set M),
   dep_coeff s (w : M) $ hnl w w.2) (@finset.univ (↑(Y \ s) : set M) _)) id,
 have hr0 : r ≠ 0 := prod_ne_zero Y s hnl hs.2.1,
  have hrX : ∀ x, x ∈ X → r • x ∈ submodule.span R (↑s : set M) := sorry,
  have hrS : ∀ x, x ∈ S → r • x ∈ submodule.span R (↑s : set M) := λ w hw,
  by {rw ←hX at hw, rw ←set.image_id (↑X : set M) at hw, rcases
  (finsupp.mem_span_iff_total R).1 hw with ⟨f, hfm, hf⟩,
  rw ←hf, rw finsupp.total_apply, rw finsupp.smul_sum,
  apply submodule.sum_mem (submodule.span R (↑s : set M)), intros c hc,
  dsimp, rw ←mul_smul, rw mul_comm, rw mul_smul,
  apply submodule.smul_mem (submodule.span R (↑s : set M)) (f c),
  exact hrX c (hfm hc)
   },
  cases free_subm (↑s : set M) set.univ s.card (by { rw univ_card s, rw finset.card_univ,
  apply fintype.card_congr, symmetry,
  exact (equiv.set.univ _).symm,
  }) (submodule.span R (↑s : set M) : set M) (λ x, ⟨x, submodule.subset_span x.2⟩)
  ⟨sorry, sorry⟩ (submodule.comap (submodule.span R (↑s : set M)).subtype
    (submodule.map (r • linear_map.id) S)) with t ht,
  let T := (λ x, r • x)⁻¹' (subtype.val '' t),
  use T,
  split, simp only [],
  unfold linear_independent at *,
  rw eq_bot_iff at *,
  by_contradiction,
  rcases submodule.not_le_iff_exists.1 a with ⟨f, hfm, hf⟩,
  refine absurd ht.1 _,
  apply submodule.not_le_iff_exists.2,
  let sset : finset t := @finset.preimage _ _ (subtype.val ∘ subtype.val)
     (finset.image (λ x : T, r • (x : M)) f.1) sorry,
  let func : t → R := λ x, f.2 ⟨r • x, sorry⟩,
  let F : t →₀ R := ⟨sset, func, sorry⟩,
  use F,
  split,
    sorry, sorry,
  ext i, split,
  intro hmem,
  sorry, sorry,
  use (↑s : set M),
  split,
  exact hs.2.1,
  rw ←hX,
  have hsY : s = Y := le_antisymm hs.1 sorry,
  rw hsY,
  sorry,
end

theorem torsion_decomp {M : Type*} [add_comm_group M] [module R M] (S : submodule R M)
  (hfg : S.fg) : ∃ t : set S, linear_independent R (λ x, x : t → S) ∧
  (tors R S) ⊓ (submodule.span R t) = ⊥ ∧ (tors R S) ⊔ (submodule.span R t) = ⊤ :=
begin
  cases free_of_tf (tors R S).quotient ⊤ (fg_quotient S hfg (tors R S))
    (tf_iff.1 $ eq_bot_iff.2 $ λ b hb, by {have := eq_bot_iff.1 (tors_free_of_quotient R S),
    rcases hb with ⟨c, hc⟩,
    have h0 : c • (b : (tors R S).quotient) = 0 := by {rw ←submodule.coe_smul,
      rw ←@submodule.coe_zero R (tors R S).quotient _ _ _ ⊤, congr, exact hc.2 },
    have ffs := this ⟨c, hc.1, h0⟩,
    rw submodule.mem_bot at ffs ⊢, rw subtype.ext_iff,
    rw ffs, refl}
    ) with t ht,
  cases (projective_of_has_basis ht S (tors R S).quotient linear_map.id (tors R S).mkq
    (λ x, quotient.induction_on' x $ λ y, ⟨y, rfl⟩)) with f hf,
  have HP := split_of_left_inv (tors R S) (tors R S).mkq (by {rw submodule.ker_mkq,
    rw submodule.range_subtype}) f (linear_map.ext hf) (submodule.range_mkq _),
  use (set.range ((f : _ → S) ∘ subtype.val : t → S)),
  split,
  apply linear_independent.to_subtype_range,
  apply linear_independent.restrict_of_comp_subtype,
  rw linear_independent_comp_subtype,
  intros l hlm hl,
  apply (linear_independent_subtype.1 ht.1 l hlm),
  rw finsupp.total_apply at *,
  apply f.to_add_monoid_hom.injective_iff.1 (function.left_inverse.injective hf),
  rw ←hl,
  erw (finset.sum_hom l.support f).symm,
  apply finset.sum_congr rfl,
  intros x hx, dsimp,
  rw linear_map.map_smul,
  convert HP, all_goals
  {rw ←set.image_univ,
  rw set.image_comp, rw submodule.span_image,
  show _ = (⊤ : submodule R (tors R S).quotient).map f,
  congr, convert ht.2, rw set.image_univ, refl},
end

def tf_basis {M : Type*} [add_comm_group M] [module R M] (S : submodule R M)
  (hfg : S.fg) := classical.some (torsion_decomp S hfg)

theorem tf_basis_is_basis {M : Type*} [add_comm_group M] [module R M] (S : submodule R M)
  (hfg : S.fg) : linear_independent R (λ x, x : tf_basis S hfg → S) :=
(classical.some_spec (torsion_decomp S hfg)).1

theorem disjoint_tors_tf {M : Type*} [add_comm_group M] [module R M] {S : submodule R M}
  (hfg : S.fg) : (tors R S) ⊓ (submodule.span R $ tf_basis S hfg) = ⊥ :=
(classical.some_spec (torsion_decomp S hfg)).2.1

theorem tors_tf_span {M : Type*} [add_comm_group M] [module R M] {S : submodule R M}
  (hfg : S.fg) : (tors R S) ⊔ (submodule.span R $ tf_basis S hfg) = ⊤ :=
(classical.some_spec (torsion_decomp S hfg)).2.2