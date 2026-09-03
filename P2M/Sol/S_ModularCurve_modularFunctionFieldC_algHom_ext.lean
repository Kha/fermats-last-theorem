import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
namespace P2MW.S_ModularCurve_modularFunctionFieldC_algHom_ext

set_option autoImplicit false

open ModularCurve

theorem solution (K : Type*) [Field K] (ℓ : ℕ) [NeZero ℓ] {A : Type*} [Semiring A] [Algebra K A]
    {f g : modularFunctionFieldC K ℓ →ₐ[K] A}
    (h1 : f ⟨jqModC K, jqModC_mem K ℓ⟩ = g ⟨jqModC K, jqModC_mem K ℓ⟩)
    (h2 : f ⟨jqNModC K ℓ, jqNModC_mem K ℓ⟩ = g ⟨jqNModC K ℓ, jqNModC_mem K ℓ⟩) : f = g := by
  refine IntermediateField.algHom_ext_of_eq_adjoin K (S := modularFunctionFieldC K ℓ)
    (s := ({jqModC K, jqNModC K ℓ} : Set (LaurentSeries K))) rfl (fun x hx => ?_)
  rcases hx with rfl | hx
  · exact h1
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact h2

#print axioms solution
