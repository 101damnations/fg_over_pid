import linear_algebra.basis

variables {R : Type*} [ring R] {M : Type*} [add_comm_group M] [module R M] {N : Type*}
  [add_comm_group N] [module R N] {M' : Type*} [add_comm_group M'] [module R M']

theorem map_inf (p p' : submodule R M) (f : M →ₗ[R] M') (hf : function.injective f) :
  p.map f ⊓ p'.map f = (p ⊓ p').map f :=
submodule.coe_injective $ set.image_inter hf

/-- We have R-submodules of M, S, T ⊆ A, where S, T are thought of as submodules of A.
Given sets s, t ⊆ M, if the submodule s generates equals 'S as a submodule of M' and the submodule
t generates equals 'T as a submodule of M', and s & t are linearly independent, and S, T are complementary
submodules of A, then s ∪ t is linearly independent and generates A. -/
theorem union_is_basis_of_gen_compl (A : submodule R M) (S : submodule R A) (s : set M)
  (T : submodule R A) (t : set M)
  (hss : submodule.span R s = S.map A.subtype) (hts : submodule.span R t = T.map A.subtype)
  (hsl : linear_independent R (λ x, x : s → M))
  (htl : linear_independent R (λ x, x : t → M))
  (h1 : S ⊓ T = ⊥) (h2 : S ⊔ T = ⊤) : linear_independent R (λ x, x : s ∪ t → M)
    ∧ submodule.span R (set.range (λ x, x : s ∪ t → M)) = A :=
begin
  split,
  apply linear_independent.union hsl htl,
  rw hss, rw hts,
  rw disjoint_iff,
  rw map_inf, rw h1, rw submodule.map_bot, exact subtype.val_injective,
  have := submodule.map_sup S T A.subtype,
  rw h2 at this,
  rw submodule.map_subtype_top at this, rw this,
  erw subtype.range_coe_subtype, rw ←hss, rw ←hts, exact submodule.span_union _ _,
end