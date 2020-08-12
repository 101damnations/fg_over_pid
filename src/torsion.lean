
import ring_theory.principal_ideal_domain linear_algebra.basic
open unique_factorization_domain

variables (R : Type*) (M : Type*) [add_comm_group M]
open_locale classical
section
variables [integral_domain R] [add_comm_group M] [module R M] (a : M)

/-- Given `a` in an R-module M, the ideal of `R` consisting of `r : R` such that
`r • a = 0`. -/
@[reducible] def ord : ideal R :=
⟨{r : R | r • a = 0}, zero_smul R a,
 λ x y (hx : _ = _) (hy : _ = _), show _ = _, by
   rw [add_smul x y a, hx, hy, zero_add],
 λ c x (h : _ = _), show _ = _, by
   rw [smul_eq_mul, ←smul_smul c x, h, smul_zero c]⟩

variables {R M}
lemma mem_ord (b : R) : b ∈ ord R M a ↔ b • a = 0 := iff.rfl

variables (R M)
/-- Torsion submodule: elements `m` of M such that there exists a non-zero `r : R` such that
`m • r = 0`. -/
def tors : submodule R M :=
⟨{a₁ : M | ∃ r : R, r ≠ 0 ∧ r ∈ ord R M a₁},
 ⟨1, ⟨ne.symm $ zero_ne_one, smul_zero 1⟩⟩,
 λ x y ⟨r, ⟨hr0, (hr : _ = _)⟩⟩ ⟨s, ⟨hs0, (hs : _ = _)⟩⟩,
  ⟨r * s, show _ ∧ (_ = _), from
   ⟨mul_ne_zero hr0 hs0, by rw [smul_add (r*s) x y, ←smul_smul r s y,
     hs, mul_comm, ←smul_smul s r]; norm_num [hr]⟩⟩,
  λ c x ⟨r, ⟨hr0, (hr : _ = _)⟩⟩,
    ⟨r, show _ ∧ (_ = _), from ⟨hr0, by rw [smul_smul r c, mul_comm,
      ←smul_smul c r, hr, smul_zero]⟩⟩⟩

end
variables [integral_domain R] [is_principal_ideal_ring R]
  [decidable_eq (associates R)] [add_comm_group M]
          [module R M] (a : M)

noncomputable instance ufd : unique_factorization_domain R :=
principal_ideal_ring.to_unique_factorization_domain

variables {R M}
--is private in mathlib
/-- Given nonzero `x : R`, if `⟦a⟧` is an element of `R` modulo association and `a` is a
factor of `x`, then `⟦a⟧` is irreducible. -/
theorem forall_map_mk_factors_irreducible (x : R) (hx : x ≠ 0) :
  ∀(a : associates R), a ∈ multiset.map associates.mk (factors x) → irreducible a :=
begin
  assume a ha,
  rcases multiset.mem_map.1 ha with ⟨c, hc, rfl⟩,
  exact (associates.irreducible_mk_iff c).2 (irreducible_factors hx _ hc)
end

/-- Given prime `p : R` and `⟦a⟧`, if `⟦a⟧` is in an i-tuple of `⟦p⟧`'s, `⟦a⟧` is irred. -/
lemma mem_repeat_prime_irred {p : R} (i : ℕ) (hp : prime p) (a : associates R)
(h : a ∈ multiset.repeat (associates.mk p) i) : irreducible a :=
by rw multiset.eq_of_mem_repeat h;
   exact (associates.irreducible_mk_iff p).2 (irreducible_iff_prime.2 hp)

/-- Given prime `p : R`, the tuple of irreducible factors of `p^i` (with multiplicity) modulo
assocition is an i-tuple of `⟦p⟧`'s. -/
lemma factors_prime_pow {p : R} (i : ℕ) (hp : prime p) :
  (factors (p^i)).map associates.mk =
  multiset.repeat (associates.mk p) i :=
associates.unique'
(forall_map_mk_factors_irreducible (p ^ i) $ pow_ne_zero i hp.1) (mem_repeat_prime_irred i hp) $
by rw [associates.prod_mk, associates.mk_eq_mk_iff_associated.2 $ factors_prod $
       pow_ne_zero i hp.1, multiset.prod_repeat, associates.mk_pow]

/-- Given prime `p : R` and the equivalence relation 'association', if `⟦r⟧` divides `⟦p ^ i⟧`, `r ≠ 0`. -/
lemma ne_zero_of_le_prime_pow {r p : R} {i : ℕ} (hp : prime p)
  (hr : associates.mk r ≤ associates.mk (p^i)) : r ≠ 0 :=
by intro h; rw h at hr; exact absurd (zero_dvd_iff.1 $
  associates.dvd_of_mk_le_mk hr) (pow_ne_zero i hp.1)

/-- Given prime `p : R` and the equivalence relation 'association', if `⟦r⟧` divides `⟦p ^ i⟧` then
there exists `j ≤ i` such that `⟦r⟧ = ⟦p ^ j⟧`. -/
lemma eq_prime_pow_of_dvd_prime_pow (r p : R) (i : ℕ) (hp : prime p)
(hr : associates.mk r ≤ associates.mk (p^i)) : ∃ j : ℕ, j ≤ i ∧ associates.mk r = associates.mk (p^j) :=
begin
  have : (factors r).map associates.mk ≤ multiset.repeat (associates.mk p) i,
  by rwa [←factors_prime_pow i hp, ←associates.prod_le_prod_iff_le
          (forall_map_mk_factors_irreducible r $ ne_zero_of_le_prime_pow hp hr) $
          forall_map_mk_factors_irreducible (p^i) $ pow_ne_zero i hp.1, associates.prod_mk,
          associates.prod_mk, associates.mk_eq_mk_iff_associated.2 $
          factors_prod $ ne_zero_of_le_prime_pow hp hr,
          associates.mk_eq_mk_iff_associated.2 $ factors_prod $ pow_ne_zero i hp.1],
  let j := multiset.card (multiset.map associates.mk $ factors r),
  exact ⟨j, ⟨by rw ←multiset.card_repeat (associates.mk p) i; exact multiset.card_le_of_le this,
    by { have H1 : multiset.map associates.mk (factors r) = multiset.repeat (associates.mk p) j,
      by rw multiset.eq_repeat'; intros; rw multiset.eq_of_mem_repeat (multiset.mem_of_le this H),
        rw [←associates.mk_eq_mk_iff_associated.2 $ factors_prod $ ne_zero_of_le_prime_pow hp hr,
            ←associates.prod_mk, H1, multiset.prod_repeat, associates.mk_pow]}⟩⟩
end

/-- if `a b : R` are equal up to association, they generate the same ideal. -/
lemma eq_span_of_eq_mk {α : Type*} [comm_ring α] {a b : α} (H: associates.mk a = associates.mk b) :
ideal.span ({a} : set α) = ideal.span ({b}) :=
begin
  apply ideal.ext, intro, split,
  intro h, cases associates.mk_eq_mk_iff_associated.1 H.symm with u hu,
  swap, intro h, cases associates.mk_eq_mk_iff_associated.1 H with u hu,
  all_goals {  cases exists_eq_mul_right_of_dvd (ideal.mem_span_singleton.1 h) with w hw,
               apply ideal.mem_span_singleton.2,
               use (↑u*w), rw [←mul_assoc, hu, hw]},
end

/-- Given `a : M` and prime `p : R` such that `p ^ i = 0`, there exists `j ≤ i` such that the ideal
generated by `p ^ j` equals the ideal of elements `r : R` such that `r • a = 0`. -/
lemma prime_pow_le (a : M) (p : R) (i : ℕ) (hp : prime p) (Ha : p^i•a = 0) :
  ∃ j : ℕ, j ≤ i ∧ ord R M a = ideal.span ({p^j}: set R) :=
begin
  rw ←submodule.is_principal.span_singleton_generator (ord R M a),
  let r := submodule.is_principal.generator (ord R M a),
  have : associates.mk r ≤ associates.mk (p^i), from
    associates.mk_le_mk_of_dvd ((submodule.is_principal.mem_iff_generator_dvd $ ord R M a).mp Ha),
  cases (eq_prime_pow_of_dvd_prime_pow r p i hp this) with j hj,
  exact ⟨j, hj.1, eq_span_of_eq_mk hj.2⟩,
end

lemma ord_ideal_zero_eq_top : ord R M 0 = ⊤ :=
eq_top_iff.2 $ λ x h, smul_zero x

/-- Given `x, y` in a torsion R-module `M`, and `n m : ℕ, p : R` such that
the ideal generated by `p ^ n` is the set of `r : R` such that `r • x = 0` and
the ideal generated by `p ^ m` is the set of `r : R` such that `r • y = 0`, we have
`p ^ max{n, m} • x + p ^ max{n, m} • y = 0`. -/
lemma pow_aux {x y : tors R M} {n m : ℕ} {p : R}
  (hn : ord R (tors R M) x = ideal.span ({p ^ n} : set R))
  (hm : ord R (tors R M) y = ideal.span ({p ^ m} : set R)) :
   p ^ max n m • x + p ^ max n m • y = 0 :=
begin
  conv in (p ^ max n m • x)
    {  rw [←nat.sub_add_cancel (le_max_left n m), pow_add p (max n m - n) n, mul_smul]},
  conv in (p ^ max n m • y)
    {  rw [←nat.sub_add_cancel (le_max_right n m), pow_add p (max n m - m) m, mul_smul]},
  suffices h : p ^ n ∈ ord R (tors R M) x ∧ p ^ m ∈ ord R (tors R M) y, by
    change _ = _ ∧ _ = _ at h; norm_num [h],
  rw [hn, hm],
  exact ⟨ideal.mem_span_singleton'.2 ⟨1, one_mul _⟩, ideal.mem_span_singleton'.2 ⟨1, one_mul _⟩⟩,
end

/-- Given `a : M` and prime `p : R`, if the ideal generated by `p ^ i` equals the set `r : R`
such that `r • a = 0`, then `p ^ i • a = 0`. -/
lemma eq_zero_of_ord_pow {a : M} {p : R} (i : ℕ) (hp : prime p)
(H : ord R M a = ideal.span ({p^i}: set R)) : p^i•a = 0 :=
show p ^ i ∈ ord R M a, by rw H; exact ideal.mem_span_singleton'.2 ⟨1, one_mul _⟩

/-- Given `a : M` and prime `p : R`, if `p ^ i • ≠ 0` and `p ^ (i + 1) • a = 0`, then the ideal
generated by `p ^ (i + 1)` equals the set of `r : R` such that `r • a = 0`. -/
lemma ord_eq_of_pow {a : M} {p : R} {i : ℕ} (hp : prime p)
  (hn0 : p ^ i • a ≠ 0) (h0 : p ^ (i + 1) • a = 0) :
  ord R M a = ideal.span ({p^(i + 1)}: set R) :=
begin
  cases prime_pow_le _ _ _ hp h0 with j hj,
  have : i + 1 ≤ j, by
    {rw ←not_lt,
    intro hnot,
    have := nat.lt_succ_iff.1 hnot,
    cases nat.le.dest this with k hk,
    rw ←hk at hn0,
    rw pow_add at hn0,
    rw mul_comm at hn0,
    rw mul_smul at hn0,
    have hj0 := eq_zero_of_ord_pow j hp hj.2,
    rw hj0 at hn0,
    rw smul_zero at hn0, exact hn0 rfl,
    },
  rw nat.le_antisymm this hj.1, exact hj.2,
end

variables (M)
/-- Given a prime `p : R`, we define a submodule of a torsion R-module comprising
`a` such that there exists `n : ℕ` for which the ideal generated by `p ^ n` equals
the set of `r : R` such that `r • a = 0`. -/
def prime_pow_ord (p : {p // prime p}) : submodule R (tors R M) :=
⟨  {a : tors R M | ∃ n : ℕ, ord R (tors R M) a = ideal.span ({p.1 ^ n} : set R)},
   ⟨0, by erw [pow_zero _, ideal.span_singleton_one, ord_ideal_zero_eq_top]⟩,
   λ x y ⟨n, (hn : _ = _)⟩ ⟨m, (hm : _ = _)⟩, by
   { cases prime_pow_le (x + y) p.1 (max n m) p.2
      (show _, by {rw smul_add (p.1 ^ (max n m)) x y, exact pow_aux hn hm}),
     exact ⟨w, h.2⟩},
    λ c x ⟨n, (hn : _ = _)⟩, by
    {  cases prime_pow_le (c•x) p.1 n p.2
       (show _, by { rw [←mul_smul, mul_comm, mul_smul],
         suffices : p.1 ^ n • x = 0, by {rw this, rw smul_zero},
          show p.1 ^ n ∈ ord R (tors R M) x, rw hn,
            exact ideal.mem_span_singleton'.2 ⟨1, one_mul _⟩}),
       exact ⟨w, h.2⟩}⟩

variables {M}

lemma exists_rep (A : submodule R M) (x : submodule.quotient A) :
∃ a : M, submodule.quotient.mk a = x := @quotient.exists_rep M (submodule.quotient_rel A) x

/-- The quotient of a module by its torsion submodule is torsion free. -/
variables (R M)
lemma tors_free_of_quotient :
  tors R (submodule.quotient $ tors R M) = ⊥ :=
by apply submodule.ext;
exact
(λ x, iff.intro
(λ h, by {rw [submodule.mem_bot], rcases h with ⟨r, ⟨hr0, hr⟩⟩,
 cases (exists_rep (tors R M) x) with a ha,
 have h : r • a ∈ tors R M, by {apply (submodule.quotient.mk_eq_zero (tors R M)).1,
                            rw [submodule.quotient.mk_smul, ha], exact hr},
        rcases h with ⟨s, ⟨hs0, hs⟩⟩,
        rw [ha.symm],
        apply (submodule.quotient.mk_eq_zero (tors R M)).2,
        exact ⟨s*r, ⟨mul_ne_zero hs0 hr0,
                        by {rw mem_ord at hs ⊢, simp [←smul_smul, hs]}⟩⟩})
(λ h, by {rw [submodule.mem_bot] at h, rw h,
          exact ⟨1, ⟨ne.symm $ zero_ne_one,
                     by {rw ord_ideal_zero_eq_top, trivial} ⟩⟩}))

/-- If `p : R` is prime, it's not nilpotent. -/
lemma ne_zero_of_prime_pow {p : R} (n : ℕ) (hp : prime p) :
  p ^ n ≠ 0 :=
begin
  induction n with n hn,
  simp,
  intro hnot,
  rw pow_succ at hnot,
  cases mul_eq_zero.1 hnot with hl hr,
  refine @not_prime_zero R _ _,
  rw ←hl, exact hp,
  exact hn hr,
end