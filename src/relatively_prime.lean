
import ring_theory.principal_ideal_domain set_lemmas linear_algebra.basic torsion
open unique_factorization_domain multiset associates

variables {R : Type*} [integral_domain R] [is_principal_ideal_ring R] [decidable_eq R]
          [decidable_eq (associates R)] (r : R)
open_locale classical

local infix ` ~ᵤ ` : 50 := associated
noncomputable theory

@[reducible] def mk' := map associates.mk (factors r)

/-- Given `r, w : R`, multiset of irreducible factors of `r` which are not associated to `w`.-/
def of_dvd' (w : R) : multiset R :=
(filter (λ x, ¬ x ~ᵤ w) $ factors r)

/-- Given `r = p₁ ^ k₁ * ... * pₙ ^ kₙ : R` with pᵢ prime, this is the finite set
`{(r / p₁ ^ k₁), ..., (r / pₙ ^ kₙ)}`. -/
def coprimes' := finset.image (multiset.prod ∘ of_dvd' r) (factors r).to_finset

variables (hr : r ≠ 0)
include hr

lemma prod_factors_eq : prod (mk' r) = associates.mk r :=
by rw [prod_mk, mk_eq_mk_iff_associated]; exact factors_prod hr

variables {w : associates R} {t : R}

/-- If t is an irred factor of r, it divides r. -/
lemma le_of_mem (t) (h : t ∈ factors r) : t ∣ r :=
begin
  have := multiset.dvd_prod h,
  rwa ←dvd_iff_dvd_of_rel_right (factors_prod hr),
end

/-- Given `r t : R`, if `i : ℕ` is the highest power to which `t` divides `r` and *`t` is irreducible*,
i.e. `r = p₁ ^ k₁ * ... * pₙ ^ kₙ * t ^ i` for some primes pᵢ and t prime, then there exist
`(q₁ ^ k₁ * ... * qₙ ^ kₙ) * (s₁ * ... * sᵢ) = r` where each `qⱼ` is associated to each `pⱼ` and each
`sⱼ` is associated to `t`. -/
lemma prod_of_dvd_eq' (t : R) :
  (of_dvd' r t).prod  * (filter (λ x, x ~ᵤ t) $ factors r).prod ~ᵤ r :=
begin
  unfold of_dvd',
  rw ←multiset.prod_add,
  rw add_comm,
  rw filter_add_not,
  exact factors_prod hr,
end

/-- For any irreducible factor `t` of `r`, if `i : ℕ` is the highest power to which
`t` divides `r` then `r \ t ^ i` divides `r`. -/
lemma of_dvd'_dvd : (of_dvd' r t).prod ∣ r :=
begin
  cases prod_of_dvd_eq' r hr t with u hu,
  rw mul_assoc at hu,
  use (filter (λ x, x ~ᵤ t) $ factors r).prod * u,
  rw hu,
end

/-- If `q ∈ coprimes' r` (see coprimes' defn), `q` divides `r`. -/
lemma le_of_mem_coprimes' (q : R) (hq : q ∈ coprimes' r) :
  q ∣ r :=
begin
  unfold coprimes' at hq,
  rw finset.mem_image at hq,
  rcases hq with ⟨i, hm, hi⟩,
  have : r ~ᵤ q * (filter (λ x, x ~ᵤ i) $ factors r).prod,
    by {rw ←hi, symmetry, convert prod_of_dvd_eq' r hr i },
  cases (associated.symm this) with u hu,
  rw mul_assoc at hu,
  use (filter (λ x, x ~ᵤ i) $ factors r).prod * u,
  exact hu.symm,
end

/-- If `r ≠ 0` and `t` divides `r`, t ≠ 0.-/
lemma ne_zero_of_dvd (h : t ∣ r) : t ≠ 0 :=
λ ht0, hr $ zero_dvd_iff.1 $ ht0 ▸ h

/-- If `r ≠ 0`, for any irreducible factor `t` of `r`, if `i : ℕ` is the highest power to which
`t` divides `r` then `r \ t ^ i ≠ 0`. -/
lemma ne_zero_of_dvd' : (of_dvd' r t).prod ≠ 0 :=
ne_zero_of_dvd r hr (of_dvd'_dvd r hr)

/-- Given 2 primes `p q : R`, if one divides the other they are associated. -/
lemma prime_dvd_prime {p q : R} (hp : prime p) (hq : prime q) (hpq : p ∣ q) : p ~ᵤ q :=
begin
  have hpq' := hpq,
  cases hpq with u hu,
  have : q ∣ p * u := ⟨1, by rw hu; rw mul_one⟩,
  cases hq.2.2 _ _ this,
  exact associated_of_dvd_dvd hpq' h,
  cases h with t ht,
  rw ht at hu,
  have H : q * (1 - p * t) = 0, by {rw mul_sub, rw ←mul_assoc, rw mul_comm q p,
    rw mul_assoc, rw ←hu, ring,},
  rw mul_eq_zero at H, cases H with h1 h2,
  exfalso,
  exact hq.1 h1,
  rw sub_eq_zero at h2,
  exfalso,
  exact hp.2.1 (is_unit_of_mul_eq_one p t h2.symm),
end

/-- For any irreducible factor `t` of `r`, if `i : ℕ` is the highest power to which
`t` divides `r` then `t` doesn't divide `r \ t ^ i`. -/
lemma not_le_of_dvd' (hm : t ∈ factors r) : ¬t ∣ (of_dvd' r t).prod :=
λ h,
begin
  rcases exists_mem_factors_of_dvd (ne_zero_of_dvd' r hr) (irreducible_factors hr t hm)
    h with ⟨q, hmq, hq⟩,
  rcases exists_mem_multiset_dvd_of_prime (prime_factors (ne_zero_of_dvd' r hr) q hmq)
  (le_of_mem (of_dvd' r t).prod (ne_zero_of_dvd' r hr) q hmq) with ⟨p, hmp, hqp⟩,
  have hp : prime p := prime_factors hr p (filter_subset _ hmp),
  have ht := associated.trans hq (prime_dvd_prime r hr (prime_factors (ne_zero_of_dvd' r hr) q hmq) hp hqp),
  exact (mem_filter.1 hmp ).2 (associated.symm ht),
end

def wtf : is_monoid_hom (associates.mk) :=
{ map_mul := λ x y : R, associates.mk_mul_mk,
  map_one := associates.one_eq_mk_one }
variables (hu : ¬is_unit r)
include hu

/-- If `r : R` isn't a unit, there exists an irreducible element dividing `r`. -/
lemma exists_mem_of_nonunit : ∃ p, p ∈ factors r :=
exists_mem_of_ne_zero
  (λ h, absurd (by rw [←is_unit_mk, is_unit_iff_eq_one, ←prod_factors_eq r hr,
  @multiset.prod_hom _ _ _ _ (factors r) (associates.mk) (wtf r hr), h, prod_zero,
    associates.one_eq_mk_one]) hu)

/-- If `r : R` isn't a unit, the set `coprimes' r` (see the defn in this file) is nonempty. -/
lemma exists_mem_coprimes'_of_nonunit : ∃ q, q ∈ coprimes' r :=
let ⟨w, h⟩ := exists_mem_of_nonunit r hr hu in
finset.nonempty_iff_ne_empty.2 (λ hn, absurd (finset.image_eq_empty.1 hn)
                             (finset.ne_empty_of_mem (mem_to_finset.2 h)))

/-- Given nonunit nonzero `r : R` and `t : R`, if for all `q` in the set
"Given `r = p₁ ^ k₁ * ... * pₙ ^ kₙ : R` with pᵢ prime, the finite set
`{(r / p₁ ^ k₁), ..., (r / pₙ ^ kₙ)}`", t divides q, then t is a unit. -/
lemma relatively_prime' (H : ∀ q ∈ coprimes' r, t ∣ q) : is_unit t :=
begin
    cases exists_mem_coprimes'_of_nonunit r hr hu,
  apply (@not_not _ _).1, assume hnu,
  have h' : t ≠ 0, by
    {intro hnu,
    exact absurd hnu (by {specialize H w h, have := le_of_mem_coprimes' r hr w h,
    exfalso, apply hr,
    rw ←zero_dvd_iff,
    rw hnu at H,
    exact dvd_trans H this,})},
   cases exists_mem_of_nonunit t h' hnu with x hx,
   have hxm : ∃ y ∈ factors r, x ~ᵤ y,
   by {apply exists_mem_factors_of_dvd hr (irreducible_factors h' x hx),
   apply dvd_trans (le_of_mem t h' x hx),
   apply dvd_trans (H w h) (le_of_mem_coprimes' r hr w h),
   },
   rcases hxm with ⟨y, hmy, hy⟩,
   cases associated.symm hy with u hu,
   have H' : x ∣ (of_dvd' r y).prod, by
   {apply dvd_trans (le_of_mem t h' x hx),
   exact H (of_dvd' r y).prod (finset.mem_image.2 (⟨y, mem_to_finset.2 hmy, rfl⟩)), },
    exact not_le_of_dvd' r hr hmy (dvd_trans (⟨u, hu.symm⟩) H'),
  apply_instance
end

omit hr hu

/-- Given `s : multiset R` and `p : R`, the multiset of elements of `s` associated to `p` is
equal modulo association to a (number-of-elements-of-s-associated-to-p)-tuple of p's, modulo
association. -/
lemma associated_pow' {n : ℕ} {s : multiset R} (h : s.card = n) {p : R} :
  map associates.mk (filter (λ x, x ~ᵤ p) s) =
  map associates.mk (repeat p (filter (λ x, x ~ᵤ p) s).card) :=
begin
  revert s,
  induction n with n hn,
  intros s h0,
  rw card_eq_zero.1 h0, simp only [filter_zero, card_zero, map_zero, repeat_zero],
  intros s hs,
  cases card_pos_iff_exists_mem.1 (by rw hs; exact n.succ_pos) with a ha,
  cases exists_cons_of_mem ha with t ht,
  rw ht,
  cases (classical.em (associated a p)),
  rw @filter_cons_of_pos R (λ x, associated x p) _ _ t h,
  rw map_cons, rw card_cons, rw repeat_succ, rw map_cons,
  rw mk_eq_mk_iff_associated.2 h,
  rw hn (by {rw ht at hs, rw card_cons at hs, exact nat.succ.inj hs}),
  rw @filter_cons_of_neg R (λ x, associated x p) _ _ t h,
  rw hn (by {rw ht at hs, rw card_cons at hs, exact nat.succ.inj hs}),
end

/-- Given multisets `s, t ⊆ R` if s equals t up to association, the product of the
elements of s is associated to the product of the elements of t. -/
lemma associated_prod {n : ℕ} {s t : multiset R} (hs : s.card = n)
  (ht : t.card = n) (h : map associates.mk s = map associates.mk t) :
  associates.mk s.prod = associates.mk t.prod :=
begin
  revert s t,
  induction n with n hn,
  intros s t hs ht h,
  rw card_eq_zero.1 hs,
  rw card_eq_zero.1 ht,
  intros s t hs ht h,
  cases card_pos_iff_exists_mem.1 (by rw hs; exact n.succ_pos) with a ha,
  cases exists_cons_of_mem ha with b hb,
  cases card_pos_iff_exists_mem.1 (by rw ht; exact n.succ_pos) with c hc,
  cases exists_cons_of_mem hc with d hd,
  rw hb, rw hd,
  rw prod_cons, rw prod_cons,
  rw ←mk_mul_mk,
  rw ←mk_mul_mk,
  rw hb at h, rw hd at h,
  rw map_cons at h, rw map_cons at h,
  rw cons_eq_cons at h,
  cases h with h h,
  have hn' := hn (by {rw hb at hs, rw card_cons at hs, exact nat.succ.inj hs})
    (by {rw hd at ht, rw card_cons at ht, exact nat.succ.inj ht}) h.2,
    rw hn', rw h.1,
    cases h with h1 h2,
    cases h2 with cs hcs,
    cases subset_map (show cs ≤ map associates.mk b, by rw hcs.1; exact le_cons_self _ _) with u hu,
  rw hu at hcs,
  rw ←map_cons at hcs, rw ←map_cons at hcs,
  have hbu := hn (by {rw hb at hs, rw card_cons at hs, exact nat.succ.inj hs})
    (show (c :: u).card = n, by {rw  ←card_map associates.mk, rw ←hcs.1,
    rw card_map,
    rw hb at hs, rw card_cons at hs, exact nat.succ.inj hs}) hcs.1,
  rw hbu, rw prod_cons,
  have hdu := hn (by {rw hd at ht, rw card_cons at ht, exact nat.succ.inj ht})
    (show (a :: u).card = n, by {rw  ←card_map associates.mk, rw ←hcs.2,
    rw card_map,
    rw hd at ht, rw card_cons at ht, exact nat.succ.inj ht}) hcs.2,
  rw hdu, rw prod_cons, rw ←associates.mk_mul_mk,
  rw ←associates.mk_mul_mk,
  rw ←mul_assoc, rw mul_comm (associates.mk a), rw mul_assoc,
end

/-- Let `r, p : R` with `p` prime. Then
`p ^ ((number of elements of a factorisation of irred factors of r associated to p) + 1)`
does not divide `r`. -/
lemma fin_pow_dvd {r p : R} (hr : r ≠ 0) (hp : prime p) :
  ¬((p ^ ((filter (λ x, associated x p) (factors r)).card + 1)) ∣ r) :=
begin
  intro h,
  cases h with z hz,
  have ha := @associated_pow' _ _ _ _ _ _ (unique_factorization_domain.factors r) rfl p,
  have ha' := associated_prod rfl (card_repeat _ _) ha,
  cases mk_eq_mk_iff_associated.1 ha' with u hu,
  rw prod_repeat at hu,
  rw pow_succ at hz,
  rw ←hu at hz,
  have hnf := @filter_add_not _ (λ x, associated x p) _ (factors r),
  have hf : (factors r).prod = ((filter (λ (x : R), x ~ᵤ p) (factors r)).prod *
    (filter (λ (a : R), ¬(λ (x : R), x ~ᵤ p) a) (factors r)).prod) := by
    {rw ←multiset.prod_add, rw hnf},
  cases (factors_prod hr) with w hw,
  conv at hz {to_lhs, rw ←hw, rw hf},
  rw ←mul_assoc p at hz,
  rw mul_comm p at hz,
  rw ←sub_eq_zero at hz,
  repeat {rw mul_assoc at hz},
  rw ←mul_sub at hz,
  have h0 := or.resolve_left (mul_eq_zero.1 hz) (by {intro hp0,
  have huh := prod_eq_zero_iff'.1 hp0,
  exact not_prime_zero ((prime_iff_of_associated (mem_filter.1 huh).2).2 hp),
  }),
  rw sub_eq_zero at h0,
  have h0' := units.eq_mul_inv_iff_mul_eq.2 h0,
  rcases exists_mem_multiset_dvd_of_prime hp (by {rw h0', exact ⟨(u : R) * z * (w⁻¹ : units R),
    by rw mul_assoc⟩}) with ⟨s, hms, hs⟩,
  have hms := mem_filter.1 hms,
  have hps := prime_dvd_prime r hr hp (prime_factors hr s hms.1) hs,
  exact hms.2 hps.symm,
end