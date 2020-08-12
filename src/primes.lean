
import relatively_prime set_lemmas linear_algebra.projection ring_theory.coprime linear_algebra.basis linear_algebra.direct_sum_module new_file tactic.abel

open_locale classical

/-- Given prime `p : R`, for all `n : ℕ`, `p ^ (n + 1)` isn't a unit.-/
lemma not_unit_of_prime_pow {R : Type*} [comm_ring R] {p : R} (hp : prime p) {n : ℕ} :
  ¬(is_unit (p ^ n.succ)) :=
begin
  intro hu,
  rw is_unit_iff_dvd_one at hu,
  exact hp.2.1 (is_unit_iff_dvd_one.2 $ dvd_trans (⟨p ^ n, by {rw ←pow_succ}⟩) hu)
end

variables (R : Type*) [integral_domain R] [is_principal_ideal_ring R]
  [decidable_eq R] [decidable_eq (associates R)]

namespace coprimes
variable (r : R)

def span := submodule.span R (↑(coprimes' r) : set R)

variables {R} (hr : r ≠ 0) (hu : ¬is_unit r)
include hr hu

lemma span_eq_top : span R r = ⊤ :=
begin
  cases submodule.is_principal.principal (span R r) with x hx,
  erw [hx, ideal.span_singleton_eq_top],
  exact relatively_prime' r hr hu
    (λ y H, by {rw ←ideal.mem_span_singleton, change _ = ideal.span {x} at hx, rw ←hx,
    exact submodule.subset_span H})
end

end coprimes

variables (R) (M : Type*) [add_comm_group M] [module R M] (A : submodule R M)

def Tp := submodule.span R $ ⋃ (p : {p : R // prime p}), (prime_pow_ord A p).1

variables {R} {α : Type*} {β : Type*} [ring α] [add_comm_group β] [module α β]

set_option class.instance_max_depth 50

lemma ord_eq (y : tors R A) : ord R A (y : A) = ord R (tors R A) y :=
submodule.ext $ λ x, ⟨λ (h : _ = _), show _ = _, from subtype.ext_iff.2 $
    by erw ←submodule.coe_smul at h; erw h; refl,
  λ (h : _ = _), show _ = _, from subtype.ext_iff.1 h⟩

variables (R)
lemma tors_gen : Tp R M A = ⊤ :=
begin
  ext,
  split,
    tauto,
  intro,
  cases classical.em (x = 0),
    rw [h, ←submodule.mem_coe], exact (Tp R M A).2,
  cases submodule.is_principal.principal (ord R (tors R A) x) with r hr,
  change _ = ideal.span {r} at hr,
  have hr0 : r ≠ 0, by
    {  assume h,
       rw [h, ideal.span_singleton_eq_bot.2 rfl] at hr,
       rcases x.2 with ⟨s, hs0, hs⟩,
       change s ∈ ord R A (x : A) at hs,
       rw ←ord_eq at hr,
       rw hr at hs,
       exact absurd ((submodule.mem_bot R).1 hs) hs0},
  have hu : ¬is_unit r, by
    {  assume hu,
       rw (ideal.span_singleton_eq_top.2 hu) at hr,
       have h1 : (1 : R) ∈ ord R (tors R A) x, from hr.symm ▸ submodule.mem_top,
       exact absurd (show x = 0, from one_smul R x ▸ set.mem_def.1 h1) h},
  cases exists_repr_of_mem_span (coprimes' r) 1
     (show (1:R) ∈ (coprimes.span R r), by rw coprimes.span_eq_top r hr0 hu; simp) with ι h1,
  rw ←one_smul R x,
  rw h1, rw finset.sum_smul, rw Tp,
  refine sum_mem_span _, intros q hq, rcases finset.mem_image.1 hq with ⟨p, hp, h⟩,
  use p,
  exact (unique_factorization_domain.prime_factors hr0 p (multiset.mem_to_finset.1 hp)),
  have hp0 : (multiset.filter (λ x, associated x p)
   (unique_factorization_domain.factors r)).prod • (ι q * q) • x = 0,
    begin
      rw ←mul_smul, rw mul_comm, rw mul_assoc, rw ←h,
      cases prod_of_dvd_eq' r hr0 p with u hu,
      rw ←units.eq_mul_inv_iff_mul_eq at hu, erw hu,
      rw mul_comm r, rw ←mul_assoc,
      rw mul_smul, convert smul_zero _,
      show r ∈ ord R (tors R A) x, rw hr, exact ideal.mem_span_singleton.2 ⟨1, (mul_one r).symm⟩,
    end,
  have H1 := @associated_pow' _ _ _ _ _ _ (unique_factorization_domain.factors r) rfl p,
  have H2 := @associated_prod _ _ _ _ _ _ (multiset.filter (λ (x : R), associated x p)
    (unique_factorization_domain.factors r))
   (multiset.repeat p (multiset.filter (λ (x : R), associated x p)
     (unique_factorization_domain.factors r)).card) rfl
   (multiset.card_repeat _ _) H1,
  cases associates.mk_eq_mk_iff_associated.1 H2 with v hv,
  rw multiset.prod_repeat at hv,
  cases prime_pow_le _ _ _ _ (by {rw ←hv, rw mul_comm, rw mul_smul, rw hp0, rw smul_zero}) with j hj,
  use j, exact hj.2, exact (unique_factorization_domain.prime_factors
    hr0 p (multiset.mem_to_finset.1 hp)),
end

instance huh {ι : Type*} (s : finset ι) : fintype (↑s : set ι) :=
fintype.of_finset s (λ x, iff.rfl)
local infix ` ~ᵤ ` : 50 := associated
variables {R}

lemma is_coprime_of_prime {p q : R} (hp : prime p) (h : ¬ p ∣ q) : is_coprime p q :=
begin
  cases submodule.is_principal.principal (ideal.span ({p, q} : set R)) with w hw,
  cases ideal.mem_span_singleton.1 (show p ∈ ideal.span {w}, by rw ideal.span;
    rw ←hw; exact submodule.subset_span (show p ∈ {p, q}, by simp only
      [set.mem_insert_iff, true_or, eq_self_iff_true])) with t ht,
  cases ideal.mem_span_singleton.1 (show q ∈ ideal.span {w}, by rw ideal.span;
    rw ←hw; exact submodule.subset_span (show q ∈ {p, q}, by simp only
      [set.mem_insert_iff, set.mem_singleton, or_true])) with r hr,
  have hwp : ¬ p ∣ w := λ hwp, h $ dvd_trans hwp ⟨r, hr⟩,
  have hwu : is_unit w := by {
    refine or.resolve_right ((irreducible_of_prime hp).2 w t ht) _,
    rintro ⟨s, hs⟩, exact hwp ⟨(s⁻¹ : units R), by {rw ht, rw ←hs,
      simp only [units.mul_inv_cancel_right],}⟩},
  rcases ideal.mem_span_pair.1 (show w ∈ ideal.span {p, q}, by rw hw;
  exact ideal.mem_span_singleton.2 (dvd_refl _)) with ⟨a, b, hab⟩,
  cases hwu with u hu,
  rw ←units.mul_right_inj u⁻¹ at hab,
  rw ←hu at hab,
  rw units.inv_mul at hab,
  rw mul_add at hab,rw ←mul_assoc at hab, rw ←mul_assoc at hab,
  use [↑u⁻¹ * a, ↑u⁻¹ * b],
  exact hab,
end

lemma prime_pow_unique {p : {p : R // prime p}} {q1 q2 : @subtype R (λ q, prime q ∧ ¬ associated q ↑p)}
  {m n : ℕ} (h0 : m ≠ 0) (h : ideal.span ({q1.1 ^ m} : set R) = ideal.span {q2.1 ^ n}) :
  associated q1.1 q2.1 ∧ m = n :=
begin
  have h1 := ideal.mem_span_singleton.1 (by rw ←h; exact ideal.mem_span_singleton.2 (dvd_refl _)),
  have h2 := ideal.mem_span_singleton.1 (by rw h; exact ideal.mem_span_singleton.2 (dvd_refl _)),
  have h12 := associated_of_dvd_dvd h1 h2,
  cases m,
  exfalso, exact h0 rfl,
  rcases unique_factorization_domain.exists_mem_factors_of_dvd (ne_zero_of_prime_pow R n q2.2.1)
    (irreducible_of_prime q1.2.1) (dvd_trans ⟨q1.1 ^ m, by rw pow_succ; refl⟩ h2) with ⟨r, hrm, hr⟩,
  have hm2 := factors_prime_pow n q2.2.1,
  have hra : associated r q2.1 := by {rw ←associates.mk_eq_mk_iff_associated,
  suffices : associates.mk r ∈ multiset.map associates.mk
    (unique_factorization_domain.factors (q2.val ^ n)), by
    {rw hm2 at this, exact multiset.eq_of_mem_repeat this},
  exact multiset.mem_map_of_mem _ hrm},
  have := associated.trans hr hra,
  split,
  exact this,
  have hunique := associates.rel_associated_iff_map_eq_map.1
  (unique_factorization_domain.unique (unique_factorization_domain.irreducible_factors $
    ne_zero_of_prime_pow R m.succ q1.2.1)
  (unique_factorization_domain.irreducible_factors $ ne_zero_of_prime_pow R n q2.2.1)
  (associated.trans (unique_factorization_domain.factors_prod (ne_zero_of_prime_pow R m.succ q1.2.1)) $
    associated.trans h12.symm
    (unique_factorization_domain.factors_prod (ne_zero_of_prime_pow R n q2.2.1)).symm)),
  rw hm2 at hunique,
  have hm1 := factors_prime_pow m.succ q1.2.1,
  rw hunique at hm1, rw ←multiset.card_repeat (associates.mk q2.1) n,
  rw ←multiset.card_repeat (associates.mk q1.1) m.succ,
  rw hm1,
end

lemma not_dvd (p : {p : R // prime p})
{l : (tors R A) →₀ R}
(hS : ↑(l.support) ⊆ (⋃ (q : { q // prime q ∧ ¬associated q ↑p}),
  (prime_pow_ord A ⟨(q.1 : R), q.2.1⟩).1))
(H : ∀ (x : (tors R A)), x ∈ l.support →
  (∃ (q : {q // prime q ∧ ¬associated q ↑p}) (n : ℕ), ord R (tors R A) x = ideal.span {(q.1 : R) ^ n})) :
  ¬ p.1 ∣ @finset.prod (↑l.support : set _) _ _
     (@finset.univ (↑l.support : set _) $ huh l.support)(λ x, (classical.some (H x x.2)).1 ^
       (classical.some (classical.some_spec $ H x x.2))) :=
begin
  set Q := @finset.prod (↑l.support : set _) _ _ (@finset.univ (↑l.support : set _) $ huh l.support)
    (λ x, (classical.some (H x x.2)).1 ^ (classical.some (classical.some_spec $ H x x.2))),
  intro hnot,
  rcases exists_mem_multiset_dvd_of_prime p.2 hnot with ⟨a, hma, ha⟩,
  cases multiset.mem_map.1 hma with y hy,
  have h0 : classical.some (classical.some_spec (H y y.2)) ≠ 0 :=
    λ h0, by {rw h0 at hy, rw pow_zero at hy, rw ←hy.2 at ha, exact p.2.2.1 (is_unit_iff_dvd_one.2 ha)},
  cases set.mem_Union.1 (hS y.2) with r hr,
  cases hr with k hk,
  have hreq : associated (classical.some (H y y.2)).1 r.1 :=
  (prime_pow_unique h0 ((classical.some_spec $ classical.some_spec $ H y.1 y.2).symm.trans hk)).1,
  have hkeq : (classical.some (classical.some_spec (H y y.2))) = k :=
  (prime_pow_unique h0 ((classical.some_spec $ classical.some_spec $ H y.1 y.2).symm.trans hk)).2,
  cases hreq.symm with u hu,
  rw hkeq at hy,
  rw ←hu at hy,
  rw ←hy.2 at ha,
  rw ←multiset.prod_repeat at ha,
  rcases exists_associated_mem_of_dvd_prod p.2 (λ b hb, by {have hb' : b = r * u :=
  @multiset.eq_of_mem_repeat _ _ _ k hb, rw hb', exact (prime_iff_of_associated ⟨u, rfl⟩).1 r.2.1,})
    ha with ⟨s, hms, hs⟩,
  rw multiset.eq_of_mem_repeat hms at hs,
  exact r.2.2 (associated.trans (⟨u, rfl⟩) hs.symm),
end

lemma trivial_inter (p : {p : R // prime p}) :
  prime_pow_ord A p ⊓ (submodule.span R $ ⋃ (q : {q : R // prime q ∧ ¬ associated q p}),
    (prime_pow_ord A ⟨q.1, q.2.1⟩).1) = ⊥ :=
begin
  rw eq_bot_iff,
  intros x hx,
  apply (submodule.mem_bot R).2,
  cases hx.1 with m hm,
  have hpm := eq_zero_of_ord_pow m p.2 hm,
  rcases (@finsupp.mem_span_iff_total (tors R A) (tors R A) R _ _ _ (@id (tors R A))
    (⋃ (q : {q : R // prime q ∧ ¬associated q ↑p}), (prime_pow_ord A ⟨q.1, q.2.1⟩).1) x).1
      (by {rw set.image_id, exact hx.2}) with ⟨l, hl, hl'⟩,
  have hS := (finsupp.mem_supported _ _).1 hl,
  cases (classical.em (l.support = ∅)),
  rw finsupp.support_eq_empty.1 h at hl',
  rw ←hl',
  rw finsupp.total_apply,
  exact finset.sum_empty,
 have H : ∀ x ∈ l.support, ∃ (q : {q : R // prime q ∧ ¬ associated q p}) (n : ℕ),
    ord R (tors R A) x = ideal.span ({q.1 ^ n} : set R) := λ y hy, set.mem_Union.1
      (hS (finset.mem_coe.2 hy)),
  cases finset.nonempty_of_ne_empty h with z hz,
  let Q := @finset.prod (↑l.support : set _) _ _ (@finset.univ (↑l.support : set _) $ huh l.support)
    (λ x, (classical.some (H x x.2)).1 ^ (classical.some (classical.some_spec $ H x x.2))),
  have HQ : Q • x = 0, by {rw ←hl', rw finsupp.total_apply, rw finsupp.smul_sum,
  rw ←@finset.sum_const_zero _ _ l.support _,
  apply finset.sum_congr rfl,
  intros y hy, dsimp,
  rw smul_comm,
  let q := classical.some (H y hy),
  let n := classical.some (classical.some_spec $ H y hy),
  let hq := classical.some_spec (classical.some_spec $ H y hy),
  suffices : q.1 ^ n ∣ Q, by {cases this with c hc, rw hc, rw mul_comm, rw mul_smul,
    rw eq_zero_of_ord_pow n q.2.1 hq,
   erw smul_zero, erw smul_zero },
  refine @dvd_prod_finset (↑l.support : set _) _ _ ⟨y, hy⟩ (λ x, (classical.some (H x x.2)).1 ^
    (classical.some (classical.some_spec $ H x x.2)))
      (@finset.univ (↑l.support : set _) $ huh l.support) _,
  exact finset.mem_univ _},
  rcases (show is_coprime (p.1 ^ m) Q, by
    {  apply is_coprime.pow_left,
    apply is_coprime_of_prime p.2,
    exact not_dvd _ _ p hS H
  }) with ⟨a, b, hab⟩,
  rw ←one_smul _ x,
  rw ←hab,
  rw add_smul,
  rw mul_smul, rw mul_smul,
  rw hpm, rw smul_zero, rw HQ, rw smul_zero, rw zero_add,
end

instance noe (Hfg : A.fg) : is_noetherian R (tors R A) :=
is_noetherian_of_submodule_of_noetherian R A (tors R A) (is_noetherian_of_fg_of_noetherian A Hfg)

noncomputable def prime_gen_set (Hfg : A.fg) (p : {p : R // prime p}) : finset (tors R A) :=
classical.some (@is_noetherian.noetherian _ _ _ _ _ (noe M A Hfg) (prime_pow_ord A p))

theorem prime_gen_set_gens (Hfg : A.fg) (p : {p : R // prime p}) :
  submodule.span R (↑(prime_gen_set M A Hfg p) : set _) = prime_pow_ord A p :=
classical.some_spec (@is_noetherian.noetherian _ _ _ _ _ (noe M A Hfg) (prime_pow_ord A p))

lemma smul_zero_of_Inf {x : R}  (Hn : Inf (set.range (ord R M)) = ideal.span ({x} : set R))
  (y : M) : x • y = 0 :=
begin
  show x ∈ ord R M y,
  apply Inf_le (show ord R M y ∈ set.range (ord R M), from ⟨y, rfl⟩),
  rw Hn,
  exact ideal.mem_span_singleton.2 (dvd_refl _),
end

lemma exists_inter (n : ℕ) (h0 : n ≠ 0) (p : R) (hp : prime p)
  (Hn : Inf (set.range (ord R M)) = ideal.span {p ^ n})
  (a : M) (ha : p ^ (n - 1) • a ≠ 0) (hna : ∃ b : M, b ∉ submodule.span R ({a} : set M)) :
  ∃ b : M, b ≠ 0 ∧ ∀ (x : M), x ∈ ((submodule.span R {a}) ⊓ (submodule.span R ({b} : set M))) → x = 0 :=
begin
  cases hna with c hc,
  have hn : p ^ n • c = 0 := by
   {have : p ^ n ∈ Inf (set.range (ord R M)), by rw Hn; exact ideal.mem_span_singleton.2 (dvd_refl _),
  have huh : Inf (set.range (ord R M)) ≤ ord R M c := Inf_le (show ord R M c ∈ set.range (ord R M),
    from ⟨c, rfl⟩),
  exact huh this},
  haveI := classical.dec_pred,
  let j := @nat.find _ (_inst _) (show ∃ n, p ^ n • c ∈ submodule.span R ({a} : set M), from ⟨n,
  by { rw hn, exact submodule.zero_mem (submodule.span R ({a} : set M))}⟩),
  have hj0 : j ≠ 0 := λ hj, absurd (show c ∈ submodule.span R {a}, by
    {rw [←one_smul _ c, ←pow_zero p, ←hj],
  exact @nat.find_spec _ (_inst _) (show ∃ n, p ^ n • c ∈ submodule.span R ({a} : set M), from ⟨n,
  by { rw hn, exact submodule.zero_mem (submodule.span R ({a} : set M)),
  }⟩),
  }) hc,
  have hj : p ^ j • c ∈ submodule.span R {a}, from @nat.find_spec _ (_inst _)
  (show ∃ n, p ^ n • c ∈ submodule.span R ({a} : set M), from ⟨n,
  by { rw hn, exact submodule.zero_mem (submodule.span R ({a} : set M)),
  }⟩),
  cases submodule.mem_span_singleton.1 hj with r₁ hr₁,
  have hjs : p ^ (j - 1) • c ∉ submodule.span R {a} := @nat.find_min _ (_inst _)
  (show ∃ n, p ^ n • c ∈ submodule.span R ({a} : set M), from ⟨n,
  by { rw hn, exact submodule.zero_mem (submodule.span R ({a} : set M)),
  }⟩) (j - 1) (nat.pred_lt hj0),
  cases (classical.em (r₁ = 0)),
  rw h at hr₁, rw zero_smul at hr₁,
  use p ^ (j - 1) • c,
  split,
  intro hpj0,
  rw hpj0 at hjs,
  exact hjs (submodule.zero_mem _),
  intros x hx,
  cases submodule.mem_span_singleton.1 hx.2 with t ht,
  rw ← @classical.not_not (x = 0),
  intro hn,
  have hpt : ¬ p ∣ t := λ ⟨m, hm⟩, by {rw hm at ht, rw mul_comm at ht, rw ←mul_smul at ht,
    rw mul_assoc at ht, rw ←pow_succ at ht, rw nat.sub_add_cancel
      (nat.succ_le_of_lt $ nat.pos_iff_ne_zero.2 hj0) at ht, rw mul_smul at ht,
        rw ←hr₁ at ht, rw smul_zero at ht, exact hn ht.symm
  },
  have hcop : is_coprime t (p ^ n) := is_coprime.symm (is_coprime.pow_left (is_coprime_of_prime hp hpt)),
  rcases hcop with ⟨z, w, hwz⟩,
  have hbeq : p ^ (j - 1) • c = (z * t) • (p ^ (j - 1) • c) + (w * (p ^ n)) • (p ^ (j - 1) • c) :=
    by {rw ←add_smul, rw hwz, rw one_smul},
  have hsb : (z * t) • (p ^ (j - 1) • c) ∈ submodule.span R ({a} : set M) :=
    by {rw mul_smul, refine submodule.smul_mem (submodule.span R ({a} : set M)) z _, rw ht, exact hx.1},
  cases submodule.mem_span_singleton.1 hsb with y hy,
  have hjm : p ^ (j - 1) • c ∈ submodule.span R ({a} : set M) := by {rw ←mul_smul (w * _) at hbeq,
  rw mul_assoc at hbeq, rw ←pow_add at hbeq,
  cases nat.le.dest (nat.succ_le_of_lt (nat.pos_iff_ne_zero.2 h0)) with l hl,
  rw add_comm at hl, rw ←hl at hbeq, rw add_assoc at hbeq, rw add_comm 1 at hbeq,
  rw nat.sub_add_cancel (nat.succ_le_of_lt (nat.pos_iff_ne_zero.2 hj0)) at hbeq,
  rw pow_add at hbeq, rw mul_smul at hbeq, rw mul_smul at hbeq, rw mul_smul at hbeq,
  rw ←hr₁ at hbeq, rw smul_zero at hbeq, rw smul_zero at hbeq, rw add_zero at hbeq,
  rw hbeq, rw ←mul_smul z t, exact hsb  },
  exact hjs hjm,
  let k := @nat.find (λ k, ¬ (p ^ (k + 1) ∣ r₁)) (_inst _)
  (by {use (multiset.filter (λ x, associated x p) (unique_factorization_domain.factors r₁)).card,
  exact fin_pow_dvd h hp }),
  have hk : p ^ k ∣ r₁ := by {
    cases (classical.em (k = 0)),
  rw h_1, rw pow_zero, exact one_dvd _,
  apply classical.not_not.1,
  intro huh,
  rw ←nat.succ_pred_eq_of_pos (nat.pos_iff_ne_zero.2 h_1) at huh,
  exact @nat.find_min _ (_inst _) (by {use (multiset.filter (λ x, associated x p)
    (unique_factorization_domain.factors r₁)).card,
  exact fin_pow_dvd h hp }) _ (nat.pred_lt h_1) huh},
  cases hk with r hr,
  have hpr : ¬ p ∣ r := λ hpr, by {cases hpr with m hm, rw hm at hr,
  rw ←mul_assoc at hr, rw mul_comm _ p at hr, rw ←pow_succ at hr, exact @nat.find_spec
    (λ k, ¬ (p ^ (k + 1) ∣ r₁)) (_inst _) (by {use (multiset.filter (λ x, associated x p)
    (unique_factorization_domain.factors r₁)).card,
  exact fin_pow_dvd h hp }) (show p ^ (k + 1) ∣ r₁, from ⟨m, by rw hr⟩)},
  have hjn :  j ≤ n := @nat.find_min' _ (_inst _) (show ∃ n, p ^ n • c ∈ submodule.span R ({a} : set M),
  from ⟨n,
  by { rw hn, exact submodule.zero_mem (submodule.span R ({a} : set M))}⟩) n
    (hn.symm ▸ (submodule.span R ({a} : set M)).zero_mem),
  have hnjk : n ≤ n - j + k := by {suffices : (p ^ (n - j + k) * r) • a = 0, by
  {rw ←not_lt, intro hnot,
  have hgh : ord R M a = ideal.span ({p ^ n} : set R) := by
    rw ←nat.sub_add_cancel (nat.succ_le_of_lt (nat.pos_iff_ne_zero.2 h0)) at ⊢ Hn;
  exact ord_eq_of_pow hp ha (smul_zero_of_Inf _ Hn a),
  cases ideal.mem_span_singleton.1 (by rw ←hgh; exact this) with w hw,
  cases nat.le.dest (nat.succ_le_of_lt hnot) with m hm,
  conv at hw {to_rhs, rw ←hm},
  rw nat.succ_eq_add_one at hw,
  rw add_assoc at hw,
  rw pow_add p (n - j + k) (1 + m) at hw,
  rw mul_assoc at hw,
  have hhh := mul_left_cancel' (ne_zero_of_prime_pow R (n - j + k) hp) hw,
  exact hpr (by {rw hhh, rw pow_add, rw mul_assoc, rw pow_one, use p ^ m * w, }),
  },
  rw ←nat.sub_add_cancel hjn at hn,
  rw pow_add at hn,
  rw mul_smul at hn,
  rw ←hr₁ at hn,
  rw hr at hn,
  rw ←mul_smul at hn,
  rw ←mul_assoc at hn,
  rw ←pow_add at hn,
  exact hn},
  have hjk : j ≤ k := by {rw ←nat.sub_le_sub_left_iff hjn, apply nat.sub_le_left_of_le_add,
    rw add_comm, exact hnjk },
  have h1j : 1 ≤ j := nat.succ_le_of_lt (nat.pos_iff_ne_zero.2 hj0),
  let b := p ^ (j - 1) • c - (r * p ^ (k - 1)) • a,
  have hpb : p • b = 0 := show p • (_ - _) = (0 : M), by
    {rw smul_sub, rw ←mul_smul, rw ←pow_succ, rw ←mul_smul, rw mul_comm r, rw ←mul_assoc, rw ←pow_succ,
    rw nat.sub_add_cancel h1j, rw nat.sub_add_cancel (le_trans h1j hjk),
   rw ←hr₁, rw hr, rw sub_self },
  use b, split,
    show _ - _ ≠ (0 : M),
    intro hb,
    rw sub_eq_zero at hb,
    apply hjs,
    rw hb,
    exact submodule.mem_span_singleton.2 ⟨r * p ^ (k - 1), rfl⟩,
  intros x hx,
  rw ← @classical.not_not (x = 0),
  intro hn,
  cases submodule.mem_span_singleton.1 hx.2 with s hs,
  have hps : ¬ p ∣ s := λ ⟨q, hq⟩, by {rw hq at hs, rw mul_comm at hs, rw mul_smul at hs,
    rw hpb at hs, rw smul_zero at hs, exact hn hs.symm},
  have hcop : is_coprime s (p ^ n) := is_coprime.symm (is_coprime.pow_left (is_coprime_of_prime hp hps)),
  rcases hcop with ⟨z, w, hwz⟩,
  have hbeq : b = (z * s) • b + (w * (p ^ n)) • b := by {rw ←add_smul, rw hwz, rw one_smul},
  have hsb : (z * s) • b ∈ submodule.span R ({a} : set M) := by {rw mul_smul,
    refine submodule.smul_mem (submodule.span R ({a} : set M)) z _, rw hs, exact hx.1},
  have hjm : p ^ (j - 1) • c ∈ submodule.span R ({a} : set M) := by
    {cases nat.le.dest (le_trans h1j hjn) with l hl,
  rw add_comm at hl, rw ←hl at hbeq, rw mul_smul at hbeq, rw pow_add at hbeq,
    rw pow_one at hbeq, rw mul_smul at hbeq, rw mul_smul at hbeq, rw hpb at hbeq, rw smul_zero at hbeq,
  rw smul_zero at hbeq, rw add_zero at hbeq,
  rw ←mul_smul at hbeq, rw ←hbeq at hsb,
  change _ - _ ∈ _ at hsb,
  rw sub_eq_add_neg at hsb,
  rw ←neg_smul at hsb,
  exact (submodule.add_mem_iff_left _ (submodule.mem_span_singleton.2 ⟨-(r * p ^ (k - 1)), rfl⟩)).1 hsb,
  },
  exact hjs hjm,
end

lemma span_quotient_iff (a : M) : A ⊔ submodule.span R {a} = ⊤ ↔
  submodule.span R ({submodule.quotient.mk a} : set A.quotient) = ⊤ :=
begin
  split,
  intro h,
  rw eq_top_iff,
  intros x hx,
  apply quotient.induction_on' x,
  intro y,
  rcases submodule.mem_sup.1 (show y ∈ A ⊔ submodule.span R ({a} : set M), by rw h;
    exact submodule.mem_top) with ⟨b, hb, c, hc, hbc⟩,
  cases submodule.mem_span_singleton.1 hc with d hd,
  rw ←hd at hbc,
  apply submodule.mem_span_singleton.2,
  use d,
  rw ←hbc,
  apply (submodule.quotient.eq _).2,
  convert (submodule.neg_mem _ hb),
  abel,
  intro h,
  rw eq_top_iff,
  intros x hx,
  apply submodule.mem_sup.2,
  cases submodule.mem_span_singleton.1 (show submodule.quotient.mk x ∈ submodule.span R
    ({submodule.quotient.mk a} : set A.quotient), by rw h; exact submodule.mem_top) with y hy,
  rw ←submodule.quotient.mk_smul at hy,
  have huh := (submodule.quotient.eq _).1 hy,
  use (x - y • a),
  split,
  convert A.neg_mem huh, abel,
  use y • a,
  split,
  exact submodule.mem_span_singleton.2 ⟨y, rfl⟩,
  rw sub_add_cancel,
end

lemma exists_compl (Hfg : A.fg) (n : ℕ) (h0 : n ≠ 0) (p : R) (hp : prime p)
  (Hn : Inf (set.range (ord R A)) = ideal.span {p ^ n})
  (a : A) (ha : p ^ (n - 1) • a ≠ 0) (hna : ∃ b : A, b ∉ submodule.span R ({a} : set A)) :
  ∃ C : submodule R A, C ⊓ submodule.span R ({a} : set A) = ⊥
    ∧ C ⊔ submodule.span R ({a} : set A) = ⊤ :=
begin
  cases (classical.em (submodule.span R ({a} : set A) = ⊤)),
    use ⊥,
    split,
      simp,
    rw h, simp,
  let S := { B : submodule R A | submodule.span R ({a} : set A) ⊓ B = ⊥ },
  have hS : set.nonempty S := by {cases exists_inter _ n h0 p hp Hn a ha hna with b hb,
  use submodule.span R ({b} : set A),
  apply eq_bot_iff.2, intros x hx, apply (submodule.mem_bot R).2, exact hb.2 x hx},
  let C := @well_founded.min (submodule R A) (>)
    (is_noetherian_iff_well_founded.1 $ is_noetherian_of_fg_of_noetherian A Hfg) S hS,
  have hAC : ∀ x : C.quotient, p ^ n • x = 0 := λ x, by {apply quotient.induction_on' x,
    intros y, erw ←submodule.quotient.mk_smul,
  rw smul_zero_of_Inf _ Hn, rw submodule.quotient.mk_zero },
  have haC : p ^ n • (@submodule.quotient.mk _ _ _ _ _ C a) = 0 := hAC _,
  have hC : submodule.span R ({a} : set A) ⊓ C = ⊥ := well_founded.min_mem
    (is_noetherian_iff_well_founded.1 $ is_noetherian_of_fg_of_noetherian A Hfg) S hS,
  have hanC : p ^ (n - 1) • (@submodule.quotient.mk _ _ _ _ _ C a) ≠ 0 :=λ ha0,
  by {rw ←submodule.quotient.mk_smul at ha0, rw submodule.quotient.mk_eq_zero at ha0,
  apply ha,rw ←submodule.mem_bot R, rw ←hC, exact ⟨submodule.mem_span_singleton.2
    ⟨p ^ (n - 1), rfl⟩, ha0⟩,
  },
  have hACn : Inf (set.range (ord R C.quotient)) = ideal.span {p ^ n} :=
  by { apply le_antisymm,
  apply Inf_le _,
  use (submodule.quotient.mk a),
  rw ←nat.sub_add_cancel (nat.succ_le_of_lt $ nat.pos_iff_ne_zero.2 h0) at haC ⊢,
  exact ord_eq_of_pow hp hanC haC,
  apply le_Inf _,
  intros b hb,
  cases hb with c hc,
  revert hc,
  apply quotient.induction_on' c,
  intros d hd,
  rw ←hd,
  intros r hr,
  cases ideal.mem_span_singleton.1 hr with s hs,
  rw hs, show _ • _ = _, rw mul_smul, exact hAC _,},
  use C,
  split,
  rw inf_comm,
  exact hC,
  rw span_quotient_iff,
  apply classical.not_not.1,
  intro HN,
  cases @exists_inter _ _ _ _ _ C.quotient _ _ n h0 p hp hACn (submodule.quotient.mk a) hanC
  (by {rcases submodule.exists_of_lt (lt_top_iff_ne_top.2 HN) with ⟨x, _, hx⟩,
  use x})
  with b hb,
  revert hb,
  apply @quotient.induction_on _ C.quotient_rel _ b,
  intros d hd,
  have hda : submodule.span R {a} ⊓ (submodule.span R {d} ⊔ C) = ⊥ := by
    {rw eq_bot_iff,
    intros x hx, apply (submodule.mem_bot R).2,
    rcases submodule.mem_sup.1 hx.2 with ⟨y, hy, z, hz, hyz⟩,
    have hyx : submodule.quotient.mk x = submodule.quotient.mk y :=
    (submodule.quotient.eq C).2 (by {rw add_comm at hyz, rw ←eq_sub_iff_add_eq at hyz,
      rw ←hyz, exact hz}),
    cases submodule.mem_span_singleton.1 hx.1 with k hk,
    cases submodule.mem_span_singleton.1 hy with j hj,
    have hd' := hd.2 (submodule.quotient.mk x) ⟨submodule.mem_span_singleton.2
      ⟨k, by {rw ←submodule.quotient.mk_smul, rw hk,}⟩, submodule.mem_span_singleton.2 ⟨j,
      by {rw hyx, erw ←submodule.quotient.mk_smul, rw hj}⟩⟩,
    apply (submodule.mem_bot R).1, rw ←hC,
    exact ⟨hx.1, (submodule.quotient.mk_eq_zero _).1 hd'⟩,
        },
  have : ∀ B, B ∈ S → ¬ C < B := λ B, well_founded.not_lt_min (is_noetherian_iff_well_founded.1 $
    is_noetherian_of_fg_of_noetherian A Hfg) S hS,
  refine this (submodule.span R {d} ⊔ C) hda _,
  rw submodule.lt_iff_le_and_exists,
  split,
  exact le_sup_right, use d,
  split,
  exact submodule.le_def.1 le_sup_left (submodule.subset_span $ set.mem_singleton d),
  intro hdC,
  rw ←submodule.quotient.mk_eq_zero at hdC,
  exact hd.1 hdC,
end

lemma Inf_eq (A : submodule R M) (s : finset M) (hs : submodule.span R (↑s : set _) = A)
 (p : R) (hp : prime p)
 (Hp : ∀ (a : M), a ∈ A ∧ a ≠ 0 → (∃! (n : ℕ), p ^ (n + 1) • a = 0 ∧ p ^ n • a ≠ 0))
 (X : M) (N : ℕ) (hN : X ∈ finset.erase s 0 ∧
    (p ^ (N + 1) • X = 0 ∧ ¬p ^ N • X = 0) ∧
      ∀ (b : M) (m : ℕ), b ∈ finset.erase s 0 ∧ p ^ (m + 1) • b = 0 ∧ ¬p ^ m • b = 0 → m ≤ N) :
  Inf (set.range (ord R A)) = ideal.span {p ^ (N + 1)} :=
begin
  have hmem : ∀ x ∈ s, x ∈ A := λ x H, hs ▸ (submodule.subset_span H),
  apply le_antisymm,
  apply Inf_le _,
  use ⟨X, hmem X $ finset.mem_of_mem_erase hN.1⟩,
  have hX : A.subtype ⟨X, hmem X $ finset.mem_of_mem_erase hN.1⟩ = X := rfl,
  exact ord_eq_of_pow hp (λ h, hN.2.1.2 $
  by {rw ←hX, rw ←linear_map.map_smul, rw h, rw linear_map.map_zero })
  (by {
    have h2 : p ^ (N + 1) • X = 0 := hN.2.1.1,
    rw ←hX at h2, rw ←linear_map.map_smul at h2,
    exact linear_map.ker_eq_bot'.1 A.ker_subtype _ h2,
    }) ,
  apply le_Inf _,
  intros c hc,
  cases hc with x hx,
  cases classical.em (x = 0),
  rw h at hx, rw ord_ideal_zero_eq_top at hx,
  rw ←hx,
  exact le_top,
  rw ←hx,
  intros y hy,
  cases ideal.mem_span_singleton.1 hy with r hr,
  cases Hp x ⟨x.2, λ h0, h $ subtype.ext_iff.2 $ h0⟩ with n hn,
  rcases (finsupp.mem_span_iff_total _).1 (show (x : M) ∈ submodule.span R (id '' (↑s : set _)), by
    rw set.image_id; rw hs; exact x.2)
  with ⟨l, hlm, hl⟩,
  rw hr,
  show _ = (0 : A),
  apply subtype.ext_iff.2, rw submodule.coe_smul, rw mul_comm,
  rw mul_smul,
  rw submodule.coe_zero,
  rw ←hl,
  rw finsupp.total_apply,
  rw finsupp.smul_sum,
  have hNs : ∀ x, x ∈ (↑s : set _) → p ^ (N + 1) • x = (0 : M) := λ z hz, by
    {cases classical.em (z = 0),
      rw h_1,
      rw smul_zero,
    cases Hp z ⟨hmem z $ finset.mem_coe.1 hz, h_1⟩ with m hm,
    cases nat.le.dest (hN.2.2 z m ⟨finset.mem_erase.2 ⟨h_1, hz⟩, hm.1⟩) with k hk,
    rw ←hk, rw add_comm m k,
    rw add_assoc,rw pow_add, rw mul_smul, rw hm.1.1, rw smul_zero},
  unfold finsupp.sum,
  convert smul_zero _,
  rw ←@finset.sum_const_zero M _ l.support _,
  apply finset.sum_congr rfl,
  intros z hz,
  rw smul_comm, convert smul_zero _,
  exact hNs z ((finsupp.mem_supported _ l).1 hlm hz),
end

lemma inf_aux {X : M} (hX : X ∈ A) {C : submodule R A}
  (hC : C ⊓ submodule.span R {⟨X, hX⟩} = ⊥ ∧ C ⊔ submodule.span R {⟨X, hX⟩} = ⊤)
{S : finset M} (hS : submodule.span R (↑S : set M) = submodule.map A.subtype C ∧
∀ (a : M), a ∈ S → submodule.span R {a} ⊓ submodule.span R (↑(S.erase a) : set M) = ⊥) :
 submodule.span R {X} ⊓ submodule.span R (↑S : set M) ≤ ⊥ :=
begin
  have := map_inf' C X hX,
  rw ←hS.1 at this,rw this,
  rw hC.1,
  rw submodule.map_bot, exact le_refl _,
end

lemma inf_aux' {X : M} (hX : X ∈ A) (hX0 : X ≠ 0) {C : submodule R A}
  (hC : C ⊓ submodule.span R {⟨X, hX⟩} = ⊥ ∧ C ⊔ submodule.span R {⟨X, hX⟩} = ⊤)
{S : finset M} (hS : submodule.span R (↑S : set _) = submodule.map A.subtype C ∧
∀ (a : M), a ∈ S → submodule.span R {a} ⊓ submodule.span R (↑(S.erase a) : set M) = ⊥)
{b : M} (hb : b ∈ S) :
  submodule.span R ({b} : set M) ⊓ submodule.span R (↑((insert X S).erase b : finset M) : set M) ≤ ⊥ :=
begin
  have H := inf_aux _ _ hX hC hS,
  have := hS.2 b hb,
  rw erase_insert_eq,
  intros z hz,
  rw insert_to_set at hz,
  rcases submodule.mem_span_insert.1 hz.2 with ⟨r, v, hvm, hv⟩,
  cases submodule.mem_span_singleton.1 hz.1 with c hc,
  have H := inf_aux _ _ hX hC hS,
  rw ←hc at hv,
  rw ←sub_eq_iff_eq_add at hv,
  have h0 : r • X = 0 := by {rw ←submodule.mem_bot R,
  apply H,
  split,
  exact submodule.mem_span_singleton.2 ⟨r, rfl⟩,
  rw ←hv,
 rw submodule.mem_coe,
 refine submodule.sub_mem _ _ _,
  apply submodule.span_mono (show {b} ⊆ S, from finset.singleton_subset_iff.2 hb),
  show c • b ∈ submodule.span R (↑({b} : finset M) : set M),
  rw finset.coe_singleton,
  exact submodule.mem_span_singleton.2 ⟨c, rfl⟩,
  exact submodule.span_mono (show S.erase b ⊆ S, from finset.erase_subset _ _) hvm,},
  rw h0 at hv, rw sub_eq_zero at hv,
  rw ←this, split,
  rw ←hc, exact submodule.mem_span_singleton.2 ⟨c, rfl⟩,
  rw ←hc, rw hv, exact hvm,
  exact hb,
  intro hXb,
  have huh := inf_of_le_left (@submodule.span_mono R _ _ _ _ _ _ (show {X} ⊆ S, by rw hXb;
    exact finset.singleton_subset_iff.2 hb)),
  change (submodule.span R (↑({X} : finset M) : set M) ⊓ submodule.span R (↑S : set M) =
    submodule.span R (↑({X} : finset M) : set M)) at huh,
  rw finset.coe_singleton at huh,
  rw huh at H,
  rw ←eq_bot_iff at H,
  erw submodule.span_singleton_eq_bot at H,
  exact hX0 H,
end

theorem gen_le (s : finset A) (hs : submodule.span R (↑s : set A) = ⊤)
  (x : A) (hx : x ∈ s) (h0 : x ≠ 0)
  (C : submodule R A) (h : is_compl C (submodule.span R {x})) :
  C = submodule.span R ((C.subtype.comp (C.linear_proj_of_is_compl (submodule.span R {x}) h) : A → A)''
    (↑(s.erase x) : set A)) :=
begin
  apply le_antisymm,
  intros y hy,
  have : (⟨y, hy⟩ : C) ∈ (C.linear_proj_of_is_compl _ h).range := by
   rw submodule.linear_proj_of_is_compl_range h; exact submodule.mem_top,
  rcases this with ⟨a, hma, ha⟩,
  have hsa : a ∈ submodule.span R (↑s : set _) := by rw hs; exact submodule.mem_top,
  rw ←set.image_id (↑s : set _) at hsa,
  rcases (finsupp.mem_span_iff_total R ).1 hsa with ⟨l, hlm, hl⟩,
  rw ←hl at ha,
  rw linear_map.map_finsupp_total at ha,
  rw finsupp.total_apply at ha,
  cases classical.em (x ∈ l.support) with hxl hxl,
  unfold finsupp.sum at ha,
  rw ←finset.insert_erase hxl at ha,
  rw finset.sum_insert (finset.not_mem_erase x l.support) at ha,
  dsimp at ha,
  rw linear_map.mem_ker.1 (show x ∈ (C.linear_proj_of_is_compl _ h).ker,
    by {rw submodule.linear_proj_of_is_compl_ker h, exact submodule.subset_span rfl}) at ha,
  rw smul_zero at ha, rw zero_add at ha,
  have huh : (⟨y, hy⟩ : C) ∈ submodule.span R ((C.linear_proj_of_is_compl (submodule.span R {x}) h) ''
    (↑(s.erase x) : _)) :=
  by {rw finsupp.mem_span_iff_total, use l.erase x, split,
    rw finsupp.mem_supported,
    rw finsupp.support_erase,
    convert finset.coe_subset.2 (finset.erase_subset_erase x hlm),
    rw finsupp.total_apply, rw ← ha, unfold finsupp.sum,
    rw finsupp.support_erase,
    refine finset.sum_congr (by {convert (eq.refl (l.support.erase x)), }) _,intros z hz,
    rw finsupp.erase_ne (finset.ne_of_mem_erase hz)
    },
  rw submodule.span_image at ⊢ huh,
  rcases huh with ⟨z, hzm, hz⟩,
  use z, split,
  exact hzm, rw subtype.ext_iff at hz, exact hz,
  unfold finsupp.sum at ha,
  rw submodule.span_image,
  rw submodule.map_comp, use ⟨y, hy⟩,
  split,
  rw ←submodule.span_image,
  apply (finsupp.mem_span_iff_total R).2, use l, split,
  intros b hb, apply finset.mem_erase.2,
  split,
  intro hbx,
  rw hbx at hb, exact hxl hb,
  exact hlm hb,
  rw finsupp.total_apply, exact ha, refl,
  intros y hy,
  rw submodule.span_image at hy,
  rcases hy with ⟨z, hzm, hz⟩,
  rw ←set.image_id (↑(s.erase x) : set A) at hzm,
  rcases (finsupp.mem_span_iff_total R).1 hzm with ⟨l, hlm, hl⟩,
  rw ←hl at hz,
  rw linear_map.map_finsupp_total at hz,
  rw finsupp.total_apply at hz, rw ←hz,
  apply submodule.sum_mem,
  intros c hc,
  apply submodule.smul_mem,
  simp only [submodule.subtype_apply, function.comp.right_id, submodule.coe_mem, linear_map.comp_apply],
end

variables {M} {R}

noncomputable def map_erase {C : submodule R A} {s : finset M} {X : M} (h : X ∈ s)
  (hs : submodule.span R (↑s : set M) = A)
(hc : is_compl C (submodule.span R {⟨X, subset_span' hs h⟩})) :=
  finset.image (A.subtype.comp (C.subtype.comp (C.linear_proj_of_is_compl
    (submodule.span R {⟨X, subset_span' hs h⟩}) hc)))
  ((subtype_mk' s (A : set M) $ (subset_span' hs)).erase ⟨X, subset_span' hs h⟩)

lemma card_map_erase {C : submodule R A} {s : finset M} {X : M} (h : X ∈ s)
  (hs : submodule.span R (↑s : set M) = A)
  (hc : is_compl C (submodule.span R {⟨X, subset_span' hs h⟩})) :
  finset.card (map_erase _ h hs hc) ≤ (s.erase X).card :=
begin
  have H : finset.card (map_erase _ h hs hc) ≤ s.card.pred := by
  {have : (map_erase _ h hs hc).card ≤
         ((subtype_mk' s ↑A (subset_span' hs)).erase ⟨X, subset_span' hs h⟩).card :=
          finset.card_image_le,
  have h' : (subtype_mk' s ↑A (subset_span' hs)).card = s.card :=
    by {unfold subtype_mk', rw univ_card s,
      refine finset.card_image_of_injective _ _,
      intros x y hxy, simp only [subtype.mk_eq_mk] at hxy, exact subtype.ext_iff.2 hxy},
  rw ←h',
  have := finset.card_erase_of_mem (show (⟨X, subset_span' hs h⟩ : A) ∈
    subtype_mk' s ↑A (subset_span' hs), from (mem_subtype_mk' (subset_span' hs)).2 $
    by {rw subtype.coe_mk, exact h}),
  rw ←this,
  exact finset.card_image_le},
  apply le_trans H,
  rw finset.card_erase_of_mem h,
end
lemma gen_le2 {C : submodule R A} {s : finset M} {X : M} (h : X ∈ s) (h0 : X ≠ 0)
  (hs : submodule.span R (↑s : set M) = A)
(hc : is_compl C (submodule.span R {⟨X, subset_span' hs h⟩})) :
  C.map A.subtype = submodule.span R (↑(map_erase _ h hs hc) : set M) :=
begin
  have := gen_le M A (subtype_mk' s (A : set M) (subset_span' hs)) (span_subtype hs)
   ⟨X, subset_span' hs h⟩ ((mem_subtype_mk' (subset_span' hs)).2 h)
    (λ hn0, h0 $ subtype.ext_iff.1 hn0) C hc,
  unfold map_erase,
  rw finset.coe_image,
  rw submodule.span_image,
  rw submodule.span_image at this,
  rw submodule.map_comp,
  exact congr_arg (submodule.map A.subtype) this,
end

lemma woohoo (n : ℕ) (s : finset M) (hs : submodule.span R (↑s : set M) = A) (hn : s.card ≤ n) :
 (∃ (p : R), prime p ∧ ∀ a : M, (a ∈ A ∧ a ≠ 0) → ∃ (n : ℕ), p ^ (n + 1) • a = 0 ∧ p ^ n • a ≠ 0) →
 ∃ (S : finset M), submodule.span R (↑S : set _) = A ∧
 ∀ a ∈ S, submodule.span R {a} ⊓ submodule.span R (↑(S.erase a) : set M) = ⊥ :=
begin
  revert A s hs hn,
  induction n with m Hm,
  intros A s hs hn H,
  rw finset.card_eq_zero.1 (nat.le_zero_iff.1 hn) at hs,
  cases H with p hp,
  use ∅,
  split,
  exact hs,
  intros a ha,
  exfalso,
  exact finset.not_mem_empty _ ha,
  intros A s hs hm htors,
  cases htors with p hp,
  have Hp : ∀ a : M, (a ∈ A ∧ a ≠ 0) → ∃! (n : ℕ), p ^ (n + 1) • a = 0 ∧ p ^ n • a ≠ 0 :=
    λ a ha, exists_unique_of_exists_of_unique (hp.2 a ha) (λ y z hy hz, by
    {rw ←(@classical.not_not (y = z)),
    intro hnot,
    wlog hyz : y < z, exact lt_or_gt_of_ne hnot,
    cases nat.le.dest (nat.succ_le_of_lt hyz) with k hk,
    apply hz.2,
    rw ←hk, rw add_comm,
    rw pow_add, rw mul_smul, rw hy.1, rw smul_zero,
    }),
  have hmem : ∀ x ∈ s, x ∈ A := λ x H, hs ▸ (submodule.subset_span H),
  cases classical.em (m = 0),
  use s,
  split,
  exact hs,
  intros a ha,
  rw h at hm,
  have h01 : s.card = 0 ∨ s.card = 1 := by {revert hm, omega},
  cases h01,
  rw finset.card_eq_zero.1 h01, simp only [finset.coe_empty, submodule.span_empty,
    finset.erase_empty, inf_bot_eq],
  cases finset.card_eq_one.1 h01 with b hb,
  rw hb at ha ⊢,
  have hab : a = b := finset.mem_singleton.1 ha,
  rw hab,
  rw singleton_erase,
  erw submodule.span_empty,
  rw inf_bot_eq,
  cases (classical.em (s.card ≤ m)) with hsm hsm,
  cases Hm A s hs hsm ⟨p, hp⟩ with S hS,
  use S, exact hS,
  replace hsm : s.card = m.succ := by omega,
  have hn0 : (s.erase 0).nonempty := by {cases classical.em ((0 : M) ∈ s) with hs0 hs0,
  have hcard := finset.card_erase_of_mem hs0,
  rw hsm at hcard, rw nat.pred_succ at hcard,
  exact finset.card_pos.1 (by {rw hcard, exact nat.pos_iff_ne_zero.2 h}),
  have heq := finset.erase_eq_of_not_mem hs0,
  exact finset.card_pos.1 (by {rw heq, rw hsm, exact nat.succ_pos _})  },
  rcases exists_max hn0 (λ a ha, Hp a ⟨hmem a $ finset.mem_of_mem_erase ha,
    finset.ne_of_mem_erase ha⟩) with ⟨X, N, hN⟩,
  dsimp at hN,
  have hX0 : (⟨X, hmem X $ finset.mem_of_mem_erase hN.1⟩ : A) ≠ 0 := λ hX0,
    finset.ne_of_mem_erase hN.1 $ subtype.ext_iff.1 hX0,
  have hX : A.subtype ⟨X, hmem X $ finset.mem_of_mem_erase hN.1⟩ = X := rfl,
  cases classical.em ((0 : M) ∈ s),
  have he0 : submodule.span R (↑(s.erase 0) : set M) = submodule.span R (↑s : set _) :=
    by {conv {to_rhs, rw ←finset.insert_erase h_1}, rw insert_to_set, rw span_insert_zero_eq, },
  exact Hm A (s.erase 0) (he0.symm ▸ hs)
    (by {rw finset.card_erase_of_mem h_1, rw hsm, rw nat.pred_succ}) ⟨p, hp⟩,
  cases classical.em (∃ b, b ∉ submodule.span R ({⟨X, hmem X $ finset.mem_of_mem_erase hN.1⟩} : set A))
    with hmA hmA,
  cases exists_compl M A ⟨s, hs⟩ (N + 1) (nat.succ_ne_zero N)
   p hp.1 (Inf_eq _ A s hs p hp.1 Hp X N hN)
   ⟨X, hmem X $ finset.mem_of_mem_erase hN.1⟩
    (by rw nat.add_sub_cancel at *; exact (λ h, hN.2.1.2 $
  by {rw ←hX, rw ←linear_map.map_smul, rw h, rw linear_map.map_zero }))
  hmA with C hC,
  have hXs : (s.erase X).card = m :=
  by {rw finset.card_erase_of_mem (finset.erase_subset 0 s hN.1), rw hsm,
      rw nat.pred_succ},
  cases Hm (C.map A.subtype) (map_erase A (finset.erase_subset 0 s hN.1) hs
    ⟨eq_bot_iff.1 hC.1, eq_top_iff.1 hC.2⟩)
    (gen_le2 A (finset.erase_subset 0 s hN.1) (finset.ne_of_mem_erase hN.1) hs
      ⟨eq_bot_iff.1 hC.1, eq_top_iff.1 hC.2⟩).symm
    (by rw ←hXs; exact card_map_erase A (finset.erase_subset 0 s hN.1) hs
      ⟨eq_bot_iff.1 hC.1, eq_top_iff.1 hC.2⟩)
    (⟨p, ⟨hp.1, λ a ha, by {rcases ha.1 with ⟨b, hmb, hb⟩, apply hp.2, split, rw ←hb,
    exact b.2, exact ha.2}⟩⟩) with S hS,
  use insert X S, split,
  rw insert_to_set, rw span_insert', rw hS.1,
 rw sup_comm,
 rw map_sup' _ _ (hmem X $ finset.mem_of_mem_erase hN.1), rw hC.2, exact submodule.map_subtype_top _,
 intros b hb,
  rw finset.mem_insert at hb,
  cases hb,
  rw hb,
  rw eq_bot_iff,
  refine le_trans _ (inf_aux _ _ (hmem X $ finset.mem_of_mem_erase hN.1) hC hS),
  exact (@inf_le_inf_left (submodule R M) _ _ _ _ (submodule.span_mono $
  show (↑((insert X S).erase X : finset M) : set M) ⊆ (↑S : set _), from
    finset.erase_insert_subset X S)),
  rw eq_bot_iff,
  exact inf_aux' _ _ (hmem X $ finset.mem_of_mem_erase hN.1) (finset.mem_erase.1 hN.1).1 hC hS hb,
  use {X},
  split,
  apply le_antisymm,
  exact submodule.span_le.2 (by {rw finset.coe_singleton, exact set.singleton_subset_iff.2
    (hmem X $ finset.mem_of_mem_erase hN.1)}),
  intros Y hY, rw ←@classical.not_not (Y ∈ submodule.span R (↑{X} : set M)),
  intro hnot,
  rw finset.coe_singleton at *,
  exact hmA ⟨⟨Y, hY⟩, λ hmnot, hnot $ (map_singleton (hmem X $ finset.mem_of_mem_erase hN.1) hY).2 hmnot⟩,
  intros a ha, erw finset.mem_singleton at ha,
  rw ha,
  erw singleton_erase,
  show _ ⊓ submodule.span R ∅ = _,
  rw submodule.span_empty,
  rw inf_bot_eq,
end

instance quotient_module (I : ideal R) : module R I.quotient :=
submodule.quotient.semimodule I

variables (R) {M}
lemma ord_eq_ker (a : M) : ord R M a = (linear_map.id.smul_right a).ker :=
begin
  ext,
  rw linear_map.mem_ker,
  refl,
end

variables {R}

def quotient_congr {A B : submodule R M} (H : A = B) : linear_equiv R A.quotient B.quotient :=
(@quotient.congr_right _ A.quotient_rel B.quotient_rel $ λ x y : M, H ▸ iff.rfl).to_linear_equiv
{ map_add := λ x y, quotient.induction_on₂' x y $ λ w z, rfl,
  map_smul := λ x y, quotient.induction_on' y $ λ w, rfl }

lemma smul_range {a : M} : (submodule.span R ({a} : set M)) = (linear_map.id.smul_right a).range :=
begin
  ext,
  rw linear_map.mem_range,
  rw submodule.mem_span_singleton,
  refl,
end

def smul_range_equiv {a : M} : linear_equiv R (submodule.span R ({a} : set M))
((@linear_map.id R R _ _ _).smul_right a).range :=
(equiv.set_congr $ submodule.ext'_iff.1 smul_range).to_linear_equiv $
{ map_add := λ x y, rfl,
  map_smul := λ c x, rfl }

noncomputable def ord_quotient (a : M) : linear_equiv R (ord R M a).quotient
  (submodule.span R ({a} : set M)) :=
(quotient_congr $ ord_eq_ker R a).trans $ (linear_map.quot_ker_equiv_range
  ((@linear_map.id R R _ _ _).smul_right a)).trans
smul_range_equiv.symm