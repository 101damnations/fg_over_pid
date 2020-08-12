import tactic linear_algebra.basis mathlib_lemmas ring_theory.principal_ideal_domain torsion
run_cmd tactic.skip
open_locale classical

variables (ι : Type*) (Rr : Type*) [integral_domain Rr]
          [decidable_eq Rr] [fintype ι]

variables (l : ι →₀ Rr)

/-- An R-module `P` is projective iff for all R-modules `A, B` and R-module homs
`f : P →ₗ[R] B, g : A →ₗ[R] B` such that g is surjective, there exists an R-module hom
`h : P →ₗ[R] B` such that `g ∘ h = f`. -/
def projective (P : Type*) [add_comm_group P] [module Rr P] := ∀ (A : Type*)
  [add_comm_group A], by exactI ∀ [module Rr A] (B : Type*), by exactI ∀ [add_comm_group B],
  by exactI ∀ [module Rr B] (f : by exactI P →ₗ[Rr] B), by exactI ∀ (g : A →ₗ[Rr] B) (h : function.surjective g),
  by exactI ∃ h : P →ₗ[Rr] A, ∀ x, g (h x) = f x

variables {Rr}

variables (Rr)
open function

/-- The short five lemma... -/
noncomputable def short_five {A : Type*} {B : Type*} {C : Type*} {D : Type*}
  {E : Type*} {F : Type*} [add_comm_group A] [add_comm_group B] [add_comm_group C]
  [add_comm_group D] [add_comm_group E] [add_comm_group F] [module Rr A] [module Rr B]
  [module Rr C] [module Rr D] [module Rr E] [module Rr F] (f : A →ₗ[Rr] B) (g : B →ₗ[Rr] C)
  (h : A ≃ₗ[Rr] D) (j : B →ₗ[Rr] E) (k : C ≃ₗ[Rr] F) (l : D →ₗ[Rr] E) (m : E →ₗ[Rr] F) (hf : f.ker = ⊥)
  (hex1 : f.range = g.ker) (hg : g.range = ⊤) (hl : l.ker = ⊥) (hex2 : l.range = m.ker)
  (hm : m.range = ⊤) (h1 : ∀ x, j (f x) = l (h x)) (h2 : ∀ x, k (g x) = m (j x)) : B ≃ₗ[Rr] E :=
linear_equiv.of_bijective j (linear_map.ker_eq_bot'.2 $ λ b H,
  begin
    obtain ⟨a, _, ha⟩ : b ∈ f.range,
      begin
        rw hex1,
        apply linear_map.mem_ker.2,
        apply linear_map.ker_eq_bot'.1 k.ker (g b),
        erw [h2 b, H, m.map_zero]
      end,
    rw ←ha,
    suffices : a = 0, from this.symm ▸ f.map_zero,
    apply linear_map.ker_eq_bot'.1 (ker_eq_bot_comp h.ker hl) a,
    erw [←h1 a, ha, H]
  end) (eq_top_iff.2 $ λ e _,
  begin
    obtain ⟨b, _, hb⟩ : m e ∈ (k.to_linear_map.comp g).range, by
      erw range_eq_top_comp hg k.range; trivial,
    obtain ⟨d, _, hd⟩ : j b - e ∈ l.range, by
      rw hex2; exact linear_map.sub_mem_ker_iff.2 (h2 b ▸ hb),
    obtain ⟨a, _, ha⟩ : d ∈ h.to_linear_map.range, by
      erw h.range; trivial,
    exact ⟨b - f a, trivial, by erw [j.map_sub, h1 a, ha, hd, sub_sub_self]⟩
  end)

/-- In an exact sequence, `Im ∂ₙ₊₁ ⊆ Ker ∂ₙ`.  -/
lemma comp_of_exact {A : Type*} {B : Type*} {C : Type*} [add_comm_group A]
  [add_comm_group B] [add_comm_group C] [module Rr A] [module Rr B] [module Rr C]
  (f : A →ₗ[Rr] B) (g : B →ₗ[Rr] C) (hex : f.range = g.ker) (x : A) : g (f x) = 0 :=
linear_map.mem_ker.1 $ by rw ←hex; exact ⟨x, trivial, rfl⟩

/-- In an SES 0 → A → B → C → 0 with maps `f, g`, if there's an R-module hom `h : C →ₗ[R] B` that's left
inverse to `g`, the SES is split. -/
noncomputable def split_of_left_inverse (A : Type*) (B : Type*) (C : Type*) [add_comm_group A]
  [add_comm_group B] [add_comm_group C] [module Rr A] [module Rr B] [module Rr C]
  (f : A →ₗ[Rr] B) (g : B →ₗ[Rr] C) (hf : f.ker = ⊥) (hg : g.range = ⊤)
  (hex : f.range = g.ker) (h : C →ₗ[Rr] B) (H : ∀ x, g (h x) = x) :
  (A × C) ≃ₗ[Rr] B :=
short_five Rr (linear_map.inl Rr A C) (linear_map.snd Rr A C) (linear_equiv.refl Rr A) (linear_map.coprod f h)
(linear_equiv.refl Rr C) f g (linear_map.ker_eq_bot'.2 $ λ x h, (prod.ext_iff.1 h).1)
(submodule.ext $ λ x, ⟨λ ⟨y, _, h⟩, linear_map.mem_ker.2 $ h ▸ rfl, λ h, ⟨x.1, trivial, prod.ext rfl $
  show 0 = x.2, from (linear_map.mem_ker.1 h).symm⟩⟩) (eq_top_iff.2 $ λ x _, ⟨⟨0, x⟩, trivial, rfl⟩)
  hf hex hg (λ x, show f x + h 0 = f x, by rw [h.map_zero, add_zero]) $
  λ x, show x.2 = g (f x.1 + h x.2), by rw [g.map_add, H x.2, comp_of_exact Rr _ _ hex, zero_add]
