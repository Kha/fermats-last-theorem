import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import P2M.Util
import P2M.Sol.S_DirectSum_toModule_injective_of_forall_diag_injective_of_isInternal

set_option autoImplicit false

open scoped DirectSum

universe u

theorem DirectSum.toModule_injective_of_forall_diag_injective_of_isInternal
    {R : Type u} [CommRing R] {H' : Type u} [AddCommGroup H'] [Module R H']
    (𝒜' : ℕ → Submodule R H') (h𝒜' : DirectSum.IsInternal 𝒜')
    (M : ℕ × ℕ → Type u) [∀ ab, AddCommGroup (M ab)] [∀ ab, Module R (M ab)]
    (Ψ : ∀ ab : ℕ × ℕ, M ab →ₗ[R] H') (hΨ : ∀ (ab : ℕ × ℕ) (x : M ab), Ψ ab x ∈ 𝒜' (ab.1 + ab.2))
    (hinj : ∀ n : ℕ, Function.Injective (DirectSum.toModule R (DoubleComplex.Diag n) H' (fun i => Ψ i.1))) :
    Function.Injective (DirectSum.toModule R (ℕ × ℕ) H' Ψ) := by p2m_exact_reverting @_root_.P2MW.S_DirectSum_toModule_injective_of_forall_diag_injective_of_isInternal.solution
