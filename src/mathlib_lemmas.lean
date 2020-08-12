import linear_algebra.finsupp

open linear_map

variables {R : Type*} {M : Type*} {M₂ : Type*} {M₃ : Type*}
variables [ring R] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃]
variables [module R M] [module R M₂] [module R M₃]
variables {α : Type*} (v : α → M)

/-- Given 2 surjective R-module homs `f : M →ₗ[R] M₂, g : M₂ →ₗ[R] M₃`, `g ∘ f` is surjective.  -/
theorem range_eq_top_comp {f : M →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃} (hf : range f = ⊤)
  (hg : range g = ⊤) : range (g.comp f) = ⊤ :=
by rw [range_comp, hf, ←hg]; refl

/-- Given 2 injective R-module homs `f : M →ₗ[R] M₂, g : M₂ →ₗ[R] M₃`, `g ∘ f` is injective.-/
theorem ker_eq_bot_comp {f : M →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃} (hf : f.ker = ⊥) (hg : g.ker = ⊥) :
  ker (g.comp f) = ⊥ :=
by rw [ker_comp, hg, ←hf]; refl
