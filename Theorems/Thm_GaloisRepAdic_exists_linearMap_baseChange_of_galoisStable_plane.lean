import Mathlib
import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_exists_linearMap_baseChange_of_galoisStable_plane

set_option autoImplicit false
open Polynomial
open scoped TensorProduct

theorem GaloisRepAdic.exists_linearMap_baseChange_of_galoisStable_plane
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M] [Module.Free O M]
    (ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End O M)
    (hcont : GaloisActionIsAdicContinuous O ρM)
    (W : Submodule K (K ⊗[O] M)) (hrank : Module.finrank K W = 2)
    (hW : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ w ∈ W,
      (ρM σ).baseChange K w ∈ W) :
    ∃ (ρ : GaloisRepAdic O) (e : ρ.V →ₗ[O] K ⊗[O] M),
      Function.Injective e ∧
      (∀ v : ρ.V, e v ∈ W) ∧
      (∀ w ∈ W, ∃ (a : O) (v : ρ.V), a ≠ 0 ∧ e v = algebraMap O K a • w) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ρ.V),
        e (ρ.ρ σ v) = (ρM σ).baseChange K (e v)) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        (LinearMap.charpoly (ρ.ρ σ)).map (algebraMap O K) =
          X ^ 2 - C (LinearMap.trace K W (((ρM σ).baseChange K).restrict (hW σ))) * X
            + C (LinearMap.det (M := ↥W) (((ρM σ).baseChange K).restrict (hW σ)))) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_exists_linearMap_baseChange_of_galoisStable_plane.solution
