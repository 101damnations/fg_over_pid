import ring_theory.principal_ideal_domain data.equiv.basic set_lemmas

variables {M : Type*} {R : Type*}
 [integral_domain R] [is_principal_ideal_ring R] [add_comm_group M]
[module R M] {A : submodule R M}
{α : Type*} {β : Type*} {γ : Type*} [add_comm_group α] [add_comm_group β]
open_locale classical
open finset

lemma sum_union_zero {s t : finset α} {f : α → β} (h : s ∩ t ⊆ {0}) (h0 : f 0 = 0) :
  finset.sum (s ∪ t) f = finset.sum s f + finset.sum t f :=
begin
  rw ←sum_union_inter,
  cases classical.em (s ∩ t = ∅) with hst hst,
  rw hst, rw sum_empty, rw add_zero,
  have : s ∩ t = {0}, from finset.subset.antisymm h (by {cases finset.nonempty_of_ne_empty hst with x hx,
  rw finset.singleton_subset_iff, convert hx, symmetry, exact finset.mem_singleton.1 (h hx)}),
  rw this, rw sum_singleton, rw h0, rw add_zero,
end

lemma sum_bind_zero {f : α → β} (h0 : f 0 = 0) {s : finset γ} {t : γ → finset α} :
  (∀x∈s, ∀y∈s, x ≠ y → (t x ∩ t y ⊆ {0})) → (finset.sum (s.bind t) f) = finset.sum s (λ x, finset.sum (t x) f) :=
finset.induction_on s (λ _, by simp only [bind_empty, finset.sum_empty])
  (assume x s hxs ih hd,
  have hd' : ∀x∈s, ∀y∈s, x ≠ y → (t x ∩ t y ⊆ {0}),
    from assume _ hx _ hy, hd _ (mem_insert_of_mem hx) _ (mem_insert_of_mem hy),
  have ∀y∈s, x ≠ y,
    from assume _ hy h, by rw [←h] at hy; contradiction,
  have ∀y∈s, (t x ∩ t y ⊆ {0}),
    from assume _ hy, hd _ (mem_insert_self _ _) _ (mem_insert_of_mem hy) (this _ hy),
  have (t x) ∩ (finset.bind s t) ⊆ {0},
    by {intros z hz, rw finset.mem_inter at hz, rcases finset.mem_bind.1 hz.2 with ⟨y, hym, hy⟩,
    exact this y hym (finset.mem_inter.2 ⟨hz.1, hy⟩)},
  by simp only [bind_insert, sum_insert hxs, sum_union_zero this h0, ih hd'])

lemma pairwise_disjoint_of_disjoint (S : set (submodule R A))
  (Hb : ∀ N ∈ S, N ⊓ submodule.span R (set.Union (λ x : S \ {N}, x.1.1)) = ⊥)
  {x y} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) : x ⊓ y ≤ ⊥ :=
begin
  rw ←Hb x hx,
  refine inf_le_inf_left _ _,
  rw submodule.span_Union,
  convert le_supr _ (⟨(y : submodule R A), (set.mem_diff _).2 ⟨hy, ne.symm hxy⟩⟩ : S \ {x}),
  exact (submodule.span_eq y).symm,
end

noncomputable def sum_mk {S : set (submodule R A)}
  (Ht : submodule.span R (set.Union (λ x : S, x.1.1)) = ⊤) (x : A) :
  A →₀ R :=
classical.some $ (finsupp.mem_span_iff_total R).1 (show x ∈ submodule.span R (id '' (set.Union (λ y : S, y.1.1))),
by {rw set.image_id, rw Ht, trivial})

lemma sum_mk_mem {S : set (submodule R A)}
  (Ht : submodule.span R (set.Union (λ x : S, x.1.1)) = ⊤) {x : A} :
  sum_mk Ht x ∈ finsupp.supported R R (set.Union (λ x : S, x.1.1)) :=
classical.some $ classical.some_spec $ (finsupp.mem_span_iff_total R).1 (show x ∈ submodule.span R (id '' (set.Union (λ y : S, y.1.1))),
by {rw set.image_id, rw Ht, trivial})

lemma sum_mk_eq {S : set (submodule R A)}
  (Ht : submodule.span R (set.Union (λ x : S, x.1.1)) = ⊤) (x : A) :
  finsupp.total _ _ _ id (sum_mk Ht x) = x :=
classical.some_spec $ classical.some_spec $ (finsupp.mem_span_iff_total R).1 (show x ∈ submodule.span R (id '' (set.Union (λ y : S, y.1.1))),
by {rw set.image_id, rw Ht, trivial})

noncomputable def G (S : set (submodule R A))
  (Ht : submodule.span R (set.Union (λ x : S, x.1.1)) = ⊤)
  (Hb : ∀ N ∈ S, N ⊓ submodule.span R (set.Union (λ x : S \ {N}, x.1.1)) = ⊥)
  (x : A) :
  Π (X : S), A →₀ R :=
   λ X, { support := finset.filter (X : set A) (sum_mk Ht x).1,
  to_fun := λ y, if y ∈ (X : submodule R A) then (sum_mk Ht x) y else 0,
  mem_support_to_fun := λ y, ⟨λ hx, by {erw if_pos (finset.mem_filter.1 hx).2,  exact ((sum_mk Ht x).3 y).1 (finset.mem_filter.1 hx).1 }, λ hx,
    by {rw finset.mem_filter, split, rw finsupp.mem_support_iff, intro hl0, apply hx, split_ifs, exact hl0, refl,
    show y ∈ (X : submodule R A), apply classical.not_not.1, intro hnot, apply hx, rw if_neg hnot,
    }⟩ }

noncomputable def v (S : set (submodule R A))
  (Ht : submodule.span R (set.Union (λ x : S, x.1.1)) = ⊤)
  (Hb : ∀ N ∈ S, N ⊓ submodule.span R (set.Union (λ x : S \ {N}, x.1.1)) = ⊥) (x : A) :
  S → A :=
λ s, finsupp.total A A R id (G S Ht Hb x s)

theorem exists_finsupp_of_mem_direct_sum
  (S : set (submodule R A))
  (Ht : submodule.span R (set.Union (λ x : S, x.1.1)) = ⊤)
  (Hb : ∀ N ∈ S, N ⊓ submodule.span R (set.Union (λ x : S \ {N}, x.1.1)) = ⊥) (x : A) :
  ∃ (l : S →₀ R), finsupp.total S A R (v S Ht Hb x) l = x :=
begin
   let F : (set.Union (λ x : S, x.1.1)) → S := λ s, classical.some (set.mem_Union.1 s.2),
  have hF : ∀ s : (set.Union (λ x : S, x.1.1)), (s : A) ∈ (F s : submodule R A) :=
    λ s, classical.some_spec (set.mem_Union.1 s.2),
  let rly : finset (set.Union (λ x : S, x.1.1)) := subtype_mk' (sum_mk Ht x).support _ (sum_mk_mem Ht),
  have hunique : ∀ (z : (set.Union (λ x : S, x.1.1))) (M N : S),
    (z : A) ∈ (M : submodule R A) → (z : A) ∈ (N : submodule R A) → ((z : A) ≠ 0) → (M = N) :=
  λ z B C hB hC h0, by {have hbB := Hb B B.2, have hbN := Hb C C.2,
  apply classical.not_not.1, intro hne, apply h0,
  rw ←@submodule.mem_bot R A _ _ _ z, rw ←hbB, split,
  exact hB, apply submodule.subset_span,
  rw set.mem_Union,
  use ⟨C, ⟨C.2, λ hmem, hne $ (subtype.ext hmem).symm⟩⟩, exact hC,},
  let lSset : finset S := finset.image F rly,
  let Lfun : S → R := λ X, if X ∈ lSset then 1 else 0,
  let L : S →₀ R := ⟨lSset, Lfun, λ y, by {split,
  intro hy, rw (show Lfun y = 1, from if_pos hy), exact one_ne_zero,
  intro hy,
  refine classical.not_not.1 _,
  intros hnot, apply hy, exact if_neg hnot,
  }⟩,
  use L,
  conv_rhs {rw ←(sum_mk_eq Ht x)}, rw finsupp.total_apply, rw finsupp.total_apply,
  unfold finsupp.sum,
   have huh : (λ X : S, L X • v S Ht Hb x X) = (λ X : S, if X ∈ lSset then v S Ht Hb x X else 0), by
    {funext, split_ifs, convert one_smul R (v S Ht Hb x X), exact if_pos h,
     convert zero_smul R (v S Ht Hb x X), exact if_neg h},
  rw huh,
  erw ←finset.sum_filter,
  show (finset.filter (λ X : S, X ∈ lSset) L.support).sum (λ X : S, (finsupp.total A A R id) (G S Ht Hb x X)) = _,
  simp only [finsupp.total_apply],
  have hse : (λ X : S, (G S Ht Hb x X).sum (λ (i : A) (a : R), a • id i)) =
       (λ X : S, (filter (X : set A) (sum_mk Ht x).1).sum (λ (i : A), (sum_mk Ht x) i • id i)) :=
    by {funext, apply finset.sum_congr rfl, intros x hx,
    congr' 1, exact if_pos (finset.mem_filter.1 hx).2},
  rw hse,
  rw finset.filter_true_of_mem,
  rw ←sum_bind_zero,
  apply finset.sum_congr,
  rw finset.image_bind,
  ext y,
  rw finset.mem_bind,
  split,
  rintro ⟨z, hzm, hz⟩,
  exact (finset.mem_filter.1 hz).1,
  intro hy,
  use ⟨y, sum_mk_mem Ht hy⟩,
  split,
  rw mem_subtype_mk', exact hy,
  rw finset.mem_filter,
  split,
  exact hy,
  exact hF ⟨y, sum_mk_mem Ht hy⟩,
  intros, refl,
  exact smul_zero _,
  intros x hx y hy hxy,
  rw ←finset.filter_and,
  intros z hz,
  rw finset.mem_singleton,
  exact pairwise_disjoint_of_disjoint _ Hb x.2 y.2 (λ hnxy, hxy $ subtype.ext hnxy) (finset.mem_filter.1 hz).2,
  intros x hx, exact hx,
end

noncomputable def gen_coeffs
  (S : set (submodule R A))
  (Ht : submodule.span R (set.Union (λ x : S, x.1.1)) = ⊤)
  (Hb : ∀ N ∈ S, N ⊓ submodule.span R (set.Union (λ x : S \ {N}, x.1.1)) = ⊥) (x) : S →₀ R :=
    classical.some $ exists_finsupp_of_mem_direct_sum S Ht Hb x

theorem gen_sum_spec
  {S : set (submodule R A)} (Ht : submodule.span R (set.Union (λ x : S, x.1.1)) = ⊤)
  (Hb : ∀ N ∈ S, N ⊓ submodule.span R (set.Union (λ x : S \ {N}, x.1.1)) = ⊥) (x : A) :
  finsupp.total S A R (v S Ht Hb x) (gen_coeffs S Ht Hb x) = x :=
  classical.some_spec $ exists_finsupp_of_mem_direct_sum S Ht Hb x

theorem mem_gen_supp {S : set (submodule R A)} (Ht : submodule.span R (set.Union (λ x : S, x.1.1)) = ⊤)
  (Hb : ∀ N ∈ S, N ⊓ submodule.span R (set.Union (λ x : S \ {N}, x.1.1)) = ⊥) (x : A) :
  x ∈ submodule.span R (set.Union (λ y : (↑(gen_coeffs S Ht Hb x).support : set S), y.1.1.1)) :=
begin
  have := gen_sum_spec Ht Hb x,
  conv_lhs {rw ←this},
  rw finsupp.total_apply,
  unfold finsupp.sum,
  refine submodule.sum_mem _ _,
  intros c hc,
  refine submodule.smul_mem _ _ _,
  unfold v, rw finsupp.total_apply,
  unfold finsupp.sum,
  refine submodule.sum_mem _ _,
  intros d hd,
  refine submodule.smul_mem _ _ _,
  change d ∈ finset.filter _ _ at hd,
  rw finset.mem_filter at hd,
  show d ∈ _,
  apply submodule.subset_span,
  rw set.mem_Union,
  use c,
  exact hc,
  exact hd.2,
end

def T {s : finset M} {S : set (submodule R A)} (Hs : submodule.span R (↑s : set M) = A) (Ht : submodule.span R (set.Union (λ x : S, x.1.1)) = ⊤)
 (Hb : ∀ N ∈ S, N ⊓ submodule.span R (set.Union (λ x : S \ {N}, x.1.1)) = ⊥) : set S :=
↑(finset.bind (subtype_mk' s A (subset_span' Hs)) (λ x : A, (gen_coeffs S Ht Hb x).support))

lemma T_mem {s : finset M} {S : set (submodule R A)} (Hs : submodule.span R (↑s : set M) = A) (Ht : submodule.span R (set.Union (λ x : S, x.1.1)) = ⊤)
 (Hb : ∀ N ∈ S, N ⊓ submodule.span R (set.Union (λ x : S \ {N}, x.1.1)) = ⊥) {x : S} :
 x ∈ T Hs Ht Hb ↔ ∃ z ∈ s, x ∈ (gen_coeffs S Ht Hb ⟨z, subset_span' Hs H⟩).support :=
begin
  split,
  intro hx,
  rcases finset.mem_bind.1 hx with ⟨y, hym, hy⟩,
  rw mem_subtype_mk' (subset_span' Hs) at hym,
  use (y : M),
  use hym,
  rw subtype.coe_eta, exact hy,
  rintro ⟨z, hzm, hz⟩,
  apply finset.mem_bind.2,
  use ⟨z, subset_span' Hs hzm⟩,
  split,
  rw mem_subtype_mk' (subset_span' Hs),
  exact hzm,
  exact hz,
end

theorem subset_gen_supp {S : set (submodule R A)} (Ht : submodule.span R (set.Union (λ x : S, x.1.1)) = ⊤)
  (Hb : ∀ N ∈ S, N ⊓ submodule.span R (set.Union (λ x : S \ {N}, x.1.1)) = ⊥) {s : finset M} (Hs : submodule.span R (↑s : set M) = A) :
  (↑s : set M) ⊆ (submodule.span R (set.Union (λ X : T Hs Ht Hb, X.1.1.1))).map A.subtype :=
begin
  intros x hx,
  have := mem_gen_supp Ht Hb ⟨x, subset_span' Hs hx⟩,
  use ⟨x, subset_span' Hs hx⟩,
  split,
  refine submodule.span_mono _ this,
  intros z hz,
  rw set.mem_Union at *,
  cases hz with i hi,
  use ⟨(i : S), by {rw T_mem Hs Ht Hb, use [x, hx, i.2]}⟩,
  convert hi, refl,
end

lemma T_subset {S : set (submodule R A)} (Ht : submodule.span R (set.Union (λ x : S, x.1.1)) = ⊤)
  (Hb : ∀ N ∈ S, N ⊓ submodule.span R (set.Union (λ x : S \ {N}, x.1.1)) = ⊥) {s : finset M} (Hs : submodule.span R (↑s : set M) = A) :
  subtype.val '' T Hs Ht Hb ⊆ S :=
begin
  intros x hx,
  rcases hx with ⟨y, hym, hy⟩,
  rw ←hy, exact y.2,
end
#check set.finite

/-- Given an f.g. R-module A and a set S of submodules whose union generates all of A,
if for all `N ∈ S`, the intersection of N and the submodule generated by union of the elements of
`S \ N` is trivial then `S` is finite. -/
theorem finite_summands_of_fg (s : finset M)
  (Hs : submodule.span R (↑s : set M) = A)
  (S : set (submodule R A))
  (Ht : submodule.span R (set.Union (λ x : S, x.1.1)) = ⊤)
  (Hb : ∀ N ∈ S, N ⊓ submodule.span R (set.Union (λ x : S \ {N}, x.1.1)) = ⊥) :
  set.finite S :=
begin
  suffices : S ⊆ insert ⊥ (subtype.val '' T Hs Ht Hb),
    by {refine set.finite.subset _ this, apply set.finite.insert, apply set.finite.image, exact finset.finite_to_set _},
  intros x hxS,
  have hTt : (submodule.span R (set.Union (λ X : T Hs Ht Hb, X.1.1.1))) = ⊤ :=
    by {apply linear_map.map_injective A.ker_subtype, rw submodule.map_subtype_top, ext y, split, rintro ⟨z, hzm, hz⟩, rw ←hz, exact z.2,
    intro hy, rw ←Hs at hy,
    refine submodule.span_le.2 _ hy,
    exact (subset_gen_supp Ht Hb Hs)},
  have hTb : ∀ N ∈ subtype.val '' T Hs Ht Hb, N ⊓ submodule.span R (set.Union (λ x : subtype.val '' T Hs Ht Hb \ {N}, x.1.1)) = ⊥ :=
  λ N hN, by {rw eq_bot_iff, refine le_trans _ (eq_bot_iff.1 $ Hb N (T_subset Ht Hb Hs hN)),
  refine inf_le_inf_left _ _,
  apply submodule.span_mono,
  intros X hX, rw set.mem_Union at hX, rcases hX with ⟨Y, hY⟩,
  rw set.mem_Union,
  use ⟨Y.1, (set.mem_diff _).2 $ ⟨T_subset Ht Hb Hs $ ((set.mem_diff _).1 Y.2).1, ((set.mem_diff _).1 Y.2).2⟩⟩,
  exact hY,},
  cases classical.em (x = ⊥),
    left, exact h,
  right,
  apply classical.not_not.1,
  intro hnot,
  apply h,
  have := Hb x hxS,
  rw ←@inf_top_eq _ _ x,
  convert this,
  symmetry,
  rw eq_top_iff,
  rw ←hTt,
  apply submodule.span_mono,
  intros Y HY,
  rw set.mem_Union at HY,
  rcases HY with ⟨Z, hZ⟩,
  rw set.mem_Union,
  use ⟨Z, (set.mem_diff _).1 $ ⟨by {apply T_subset Ht Hb Hs, use Z, split, exact Z.2, refl},
     λ hnotZ, by {apply hnot, use Z, split, exact Z.2, exact hnotZ}⟩⟩,
  exact hZ,
end