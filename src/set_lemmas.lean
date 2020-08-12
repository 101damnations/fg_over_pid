import data.set.basic data.set.lattice data.finset ring_theory.principal_ideal_domain

variables {R : Type*} {M : Type*} [integral_domain R]
[is_principal_ideal_ring R] [add_comm_group M] [module R M] {A : submodule R M}

open_locale classical

theorem not_mem_diff_singleton {α : Type*} {s : set α} {x : α} : x ∉ s \ {x} :=
λ h, set.not_mem_of_mem_diff h (set.mem_singleton x)

lemma insert_to_set' {α : Type*} {s : finset α} {a : α} :
   (↑(insert a s) : set α) = insert a (↑s : set α) :=
begin
  ext,
  erw finset.mem_coe,
  rw set.mem_insert_iff,
  rw finset.mem_insert,
  refl,
end

lemma subset_singleton {M : Type*} {c : M} {l : finset M} (h : l ⊆ {c}) : l = ∅ ∨ l = {c} :=
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

/-- Given a function `f : α → β` and multisets `s ⊆ β, t ⊆ α`, if `s ⊆ f's image on t`, there
exists a multiset `u ⊆ α` such that f's image on u equals s. -/
lemma subset_map {α : Type*} {β : Type*} {f : α → β} {s : multiset β}
  {t : multiset α} (h : s ≤ multiset.map f t) : ∃ u : multiset α, s = multiset.map f u :=
begin
  revert f,
  apply multiset.induction_on s,
  intros f hf, use 0, exact multiset.map_zero f,
  intros a s hf f hs,
  cases multiset.mem_map.1 (show a ∈ multiset.map f t, from multiset.mem_of_le hs (multiset.mem_cons_self a s)),
  cases hf (le_trans (multiset.le_cons_self s a) hs) with u hu,
  use w :: u,
  rw multiset.map_cons,
  rw h.2, rw ←hu,
end

theorem eq_insert_erase_of_mem {α : Type*} (s : set α) (x : α) (hx : x ∈ s) :
  s = insert x (s \ {x}) :=
begin
  symmetry,
  rw set.insert_diff_singleton,
  exact set.insert_eq_of_mem hx,
end

theorem submodule_eq_bot {M : Type*} (R : Type*) [integral_domain R]
  [is_principal_ideal_ring R] [add_comm_group M]
  [module R M] (A : submodule R M) (h : A = ⊥ )
   (S : submodule R A) : S = ⊥ :=
begin
  ext,
  split,
  intro hx,
  cases x with x1 x2,
  rw submodule.mem_bot,
  rw subtype.ext_iff,
  rw h at x2,
  exact (submodule.mem_bot R).1 x2,
  intro hx,
  rw submodule.mem_bot at hx,
  rw hx,
  exact S.zero_mem,
end

/-- Given a multiset s of elements of an integral domain, the product of elements of s equals
zero iff zero is in s. -/
theorem prod_eq_zero_iff' {α : Type*} [integral_domain α] {s : multiset α} :
  s.prod = 0 ↔ (0 : α) ∈ s :=
begin
  apply multiset.induction_on s,
  simp only [iff_self, one_ne_zero, multiset.not_mem_zero, multiset.prod_zero],
  intros a s h,
  rw multiset.prod_cons,split,
  intro h0,
  cases mul_eq_zero.1 h0,
  rw h_1, exact multiset.mem_cons_self _ _,
  exact multiset.mem_cons.2 (or.inr $ h.1 h_1),
  intro h0,
  cases multiset.mem_cons.1 h0,
  rw ←h_1,
  rw zero_mul,
  rw h.2 h_1,
  exact mul_zero a,
end

/-- Given a finset s of elements of an integral domain, the product of elements of s equals
zero iff zero is in s. -/
theorem finset_prod_eq_zero_iff {α : Type*} [integral_domain α] {s : finset α} :
  s.prod id = 0 ↔ (0 : α) ∈ s :=
begin
  erw prod_eq_zero_iff',
  erw multiset.map_id', refl,
end

lemma exists_repr_of_mem_span {α : Type*} [comm_ring α] : ∀ (s : finset α) (x : α),
  x ∈ submodule.span α (↑s : set α) → ∃ ι : α → α, x = s.sum (λ r, (ι r) * r) :=
begin
  intro s,
  apply finset.induction_on s,
    intros,
    rw [finset.coe_empty, submodule.span_empty] at a,
    use id,
    rw (submodule.mem_bot α).1 a, simp,
  intros x t h H y hy,
  rw finset.coe_insert at hy,
  rcases ideal.mem_span_insert.1 hy with ⟨a, z, hz, hs⟩,
  cases H z hz with τ hn,
  rw [hs, hn],
  use (λ b, ite (b ∈ t) (τ b) a),
  rw finset.sum_insert h,
  split_ifs,
  rw add_right_inj,
  apply finset.sum_congr,
    simp,
  intros b hb,
  split_ifs,
  simp,
end

lemma sum_mem_span {α : Type*} [ring α]
  {M : Type*} {R : Type*}
  [ring R] [add_comm_group M] [module R M] {ι : R → R}
  {x : M} {c : finset R} {p : set α} {f : p → submodule R M}
  (H : ∀ s ∈ c, ∃ m, (ι s * s) • x ∈ f m) :
  c.sum (λ y, (ι y * y) • x) ∈ submodule.span R (⋃ m, (f m).carrier) :=
begin
  refine submodule.sum_mem _ _,
  intros y hy,
  cases H y hy with m hm,
  apply submodule.subset_span, apply set.mem_Union.2,
  use m, exact hm,
end

lemma dvd_prod_finset {α : Type*}{β : Type*} [comm_semiring β]
  {a : α} {f : α → β} {s : finset α} : a ∈ s → f a ∣ s.prod f :=
begin
  intro h,
  use (s.erase a).prod f,
  conv {to_lhs, rw ←finset.insert_erase h},
  rw finset.prod_insert (finset.not_mem_erase _ _),
end

lemma insert_to_set {α : Type*} {s : finset α} {a : α} :
  (↑(insert a s) : set α) = insert a (↑s : set _) :=
begin
  ext,
  erw finset.mem_coe,
  rw set.mem_insert_iff,
  rw finset.mem_insert,
  refl,
end

lemma span_insert (s t : finset M) (hs : submodule.span R (↑s : set _) = A)
  (x : M) (hx : x ∈ s)
  (ht : submodule.span R (↑t : set _) = submodule.span R (↑(s.erase x) : set M)) :
  submodule.span R (↑(insert x t) : set _) = A :=
begin
  ext y,
  split,
  intro h,
  rw insert_to_set at h,
  rcases submodule.mem_span_insert.1 h with ⟨z, b, hb, hbz⟩,
  rw ←hs,
  rw ←finset.insert_erase hx,
  rw insert_to_set,
  rw submodule.mem_span_insert,
  use z, use b, split,
  rw ←ht, exact hb,
  exact hbz,
  intro h,
  rw insert_to_set,
  rw submodule.mem_span_insert,
  rw ←hs at h,
  rw ←finset.insert_erase hx at h,
  rw insert_to_set at h,
  rcases submodule.mem_span_insert.1 h with ⟨z, b, hb, hbz⟩,
  use z, use b,
  split,
  rw ht,
  exact hb,
  exact hbz,
end

lemma span_insert' (s : set M) (a : M) :
  submodule.span R (insert a s) = submodule.span R s ⊔ submodule.span R {a} :=
begin
  rw ←submodule.span_union,
  rw set.union_singleton,
end

lemma singleton_erase {α : Type*} (a : α) : ({a} : finset α).erase a = ∅ :=
finset.erase_insert (finset.not_mem_empty _)

lemma mem_max {α : Type*}
  (s : finset α) (h : s.nonempty) (f : α → ℕ) :
  ∃ x ∈ s, finset.fold max 0 f s = f x :=
begin
  unfreezingI {revert h},
  apply finset.induction_on s,
  intro h, exfalso,
  cases h with x hx,
  exact hx,
  intros y s hy hs h,
  cases (classical.em s.nonempty) with H H,
  rcases hs H with ⟨x, hxm, hx⟩,
  have := @finset.fold_insert_idem α ℕ max _ _ f 0 s y _ _,
  unfold max at this,
  cases (classical.em (finset.fold max 0 f s ≤ f y)) with hl hr,
  rw if_pos hl at this,
  use y, split, exact finset.mem_insert.2 (or.inl rfl),
  rw this,
  rw if_neg hr at this,
  use x, split,
  exact finset.mem_insert.2 (or.inr hxm),
  rw this, rw hx,
  have : s = ∅ := or.resolve_right s.eq_empty_or_nonempty H,
  use y, split,
  exact finset.mem_insert.2 (or.inl rfl),
  rw this, erw finset.fold_singleton,
  unfold max, rw if_pos, exact nat.zero_le _,
end

lemma exists_max {α : Type*}
  {s : finset α} (hs : s.nonempty) {P : α → ℕ → Prop}
  (h : ∀ a, a ∈ s → ∃! n, P a n) : ∃ (a : α) (n : ℕ), a ∈ s ∧
  P a n ∧ (∀ (b : α) (m : ℕ), b ∈ s ∧ P b m → m ≤ n) :=
begin
  rcases mem_max s hs (λ a, if ha : a ∈ s then
    classical.some (h a ha) else 0) with ⟨x, hxm, hx⟩,
  set N := finset.fold max 0 (λ a, if ha : a ∈ s then
    classical.some (h a ha) else 0) s,
  use x,
  use N,
  split,
  exact hxm,
  split,
  dsimp at hx,
  erw dif_pos hxm at hx,
  rw hx,
  exact (classical.some_spec (h x hxm)).1,
  intros b m hb,
  rw finset.le_fold_max m,
  right,
  use b,
  split,
  exact hb.1,
  rw dif_pos hb.1,
  rw ←(classical.some_spec (h b hb.1)).2 m hb.2,
end

lemma span_insert_zero_eq {s : set M} :
  submodule.span R (insert (0 : M) s) = submodule.span R s :=
begin
  rw ←set.union_singleton,
  rw submodule.span_union,
  rw submodule.span_singleton_eq_bot.2 rfl,
  rw sup_bot_eq,
end

lemma map_inf' (C : submodule R A) (x : M) (hx : x ∈ A) :
  submodule.span R {x} ⊓ C.map A.subtype = (C ⊓ submodule.span R {⟨x, hx⟩}).map A.subtype :=
begin
  rw inf_comm,
  convert submodule.map_inf_eq_map_inf_comap,
  ext y,
  split,
  intro h,
  cases submodule.mem_span_singleton.1 h with c hc,
  exact submodule.mem_span_singleton.2 ⟨c, by {rw ←hc, rw A.subtype.map_smul, refl,}⟩,
  intro h,
  cases submodule.mem_span_singleton.1 h with c hc,
  exact submodule.mem_span_singleton.2 ⟨c, subtype.ext_iff.2 $
    by {rw ←(show c • x = (y : M), from hc), refl,}⟩
end

lemma map_sup' (C : submodule R A) (x : M) (hx : x ∈ A) :
  submodule.span R {x} ⊔ C.map A.subtype = (C ⊔ submodule.span R {⟨x, hx⟩}).map A.subtype :=
begin
  rw submodule.map_sup,
  rw sup_comm,
  congr,
    ext y,
    split,
    intro h,
     cases submodule.mem_span_singleton.1 h with c hc,
    exact ⟨c • ⟨x, hx⟩, submodule.mem_span_singleton.2 ⟨c, rfl⟩, by {rw ←hc, refl}⟩,
  intro h, rcases h with ⟨z, hzm, hz⟩,
  cases submodule.mem_span_singleton.1 hzm with c hc,
  exact submodule.mem_span_singleton.2 ⟨c, by {rw ←hz, rw ←hc, refl}⟩,
end

lemma map_singleton {x y : M} (hx : x ∈ A) (hy : y ∈ A) :
  y ∈ submodule.span R ({x} : set M) ↔ (⟨y, hy⟩ : A) ∈ submodule.span R ({⟨x, hx⟩} : set A) :=
begin
  rw submodule.mem_span_singleton, rw submodule.mem_span_singleton,
  split,
  rintro ⟨r, hr⟩,
  use r, apply subtype.ext_iff.2,
  dsimp, exact hr,
  rintro ⟨r, hr⟩,
  use r,
  rw subtype.ext_iff at hr,
  dsimp at hr,
  rw ←hr,
end

lemma erase_insert_eq {S : finset M} {x b : M} (h : b ∈ S) (hx : x ≠ b) :
  (insert x S).erase b = insert x (S.erase b) :=
begin
  ext y,
  split,
  intro hy,
  cases finset.mem_insert.1 (finset.erase_subset _ _ hy) with h1 h2,
  exact finset.mem_insert.2 (or.inl h1),
  refine finset.mem_insert.2 (or.inr _),
  rw finset.mem_erase, split,
  exact (finset.mem_erase.1 hy).1, exact h2,
  intro hy,
  cases finset.mem_insert.1 hy with h1 h2,
  rw finset.mem_erase,
  split,
  rw h1, exact hx,
  exact finset.mem_insert.2 (or.inl h1),
  rw finset.mem_erase,
  split,
  exact (finset.mem_erase.1 h2).1,
  exact finset.mem_insert.2 (or.inr (finset.erase_subset _ _ h2)),
end

lemma subset_span' {s : finset M} (hs : submodule.span R (↑s : set M) = A) :
  (↑s : set M) ⊆ A :=
λ x hx, by rw ←hs; exact submodule.subset_span hx

noncomputable def subtype_mk' {α : Type*} (s : finset α) (t : set α) (h :  (↑s : set α) ⊆ t) :
  finset t :=
finset.image (λ x : (↑s : set α), ⟨x.1, h x.2⟩) finset.univ

lemma mem_subtype_mk' {α : Type*} {s : finset α} {t : set α} (h :  (↑s : set α) ⊆ t) {x} :
  x ∈ subtype_mk' s t h ↔ (x : α) ∈ s :=
begin
  unfold subtype_mk',
  rw finset.mem_image,
  split, rintro ⟨y, hmy, hy⟩,
  rw ←hy,
  exact y.2,
  intro hx,
  use ⟨x, hx⟩,
  split,
  exact finset.mem_univ _,
  simp only [subtype.coe_eta],
end

lemma subtype_ne {α : Type*} {p : α → Prop} {x y : subtype p} :
  (x : α) ≠ y ↔ x ≠ y :=
⟨λ hn h, hn $ h ▸ rfl, λ hn h, hn $ subtype.ext h⟩

lemma subtype_mk'_erase {α : Type*} {s : finset α} {t : set α} (h :  (↑s : set α) ⊆ t) {x} (hx : x ∈ s):
  subtype_mk' (s.erase x) t (set.subset.trans (finset.erase_subset x s) h) =
  (subtype_mk' s t h).erase ⟨x, h hx⟩ :=
begin
  ext,
  rw finset.mem_erase,
  rw mem_subtype_mk', rw mem_subtype_mk',
  rw ←subtype_ne,
  exact finset.mem_erase,
end

lemma subtype_mk'_insert {α : Type*} [decidable_eq α] {s : finset α} {t : set α} (h :  (↑s : set α) ⊆ t) {x} (hx : x ∈ t) :
  subtype_mk' (insert x s) t (by {rw finset.coe_insert, exact set.insert_subset.2 ⟨hx, h⟩}) = insert (⟨x, hx⟩ : t) (subtype_mk' s t h) :=
begin
  ext y,
  split,
  intro H,
  rw mem_subtype_mk' at H,
  cases finset.mem_insert.1 H with hl hr,
  rw finset.mem_insert, left,
  apply subtype.ext,
  exact hl,
  rw finset.mem_insert, right,
  exact (mem_subtype_mk' _).2 hr,
  intro H,
  cases finset.mem_insert.1 H with hl hr,
  rw mem_subtype_mk',
  rw finset.mem_insert,
  left,
  rw hl,
  refl,
  rw mem_subtype_mk' at hr ⊢,
  rw finset.mem_insert,
  right,
  exact hr,
end

lemma span_subtype {s : finset M} (h : submodule.span R (↑s : set M) = A) :
  submodule.span R (↑(subtype_mk' s A (subset_span' h)) : set A) = ⊤ :=
begin
  have : (↑s : set M) = A.subtype '' (↑(subtype_mk' s A (h ▸ submodule.subset_span)) : set A) :=
    by {
    ext, split, intro hx, simp, exact
      ⟨by {rw ←h, exact ⟨x, submodule.subset_span hx⟩},
      by {unfold subtype_mk', erw finset.mem_image, use x, exact hx, split, exact finset.mem_univ _,
      cases h, refl, cases h, refl}⟩,
    rintro ⟨y, hym, hy⟩,
    dsimp at hy, rw ←hy, erw mem_subtype_mk' at hym, exact hym},
  rw this at h, rw submodule.span_image at h,
  apply linear_map.map_injective A.ker_subtype,
  rw A.map_subtype_top, exact h,
end

lemma card_indep {α : Type*} {s : set α} [h1 : fintype s] (h : s.finite) :
  @fintype.card s h1 = @fintype.card s (set.finite.fintype h) :=
begin
  finish,
end

lemma univ_card {α : Type*} (s : finset α) : s.card = (@finset.univ (↑s : set α) _).card :=
begin
  rw finset.card_univ,
  simp only [fintype.card_coe],
end

lemma univ_card'' {α : Type*} {h1 : fintype (@set.univ α)} {h : fintype α} : @fintype.card (@set.univ α) h1 = fintype.card α :=
begin
  rw ←fintype.of_equiv_card (equiv.set.univ α), finish,
end

theorem card_insert' {α : Type*} {a : α} (s : set α)
  {h1 : fintype s} (h : a ∉ s) {d : fintype (insert a s : set α)} :
  @fintype.card _ d = fintype.card s + 1 :=
by rw ← set.card_fintype_insert' s h; congr