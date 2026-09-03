import Mathlib
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GroupCohomology_TangentSpace
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_detIsCyclotomic_iff_forall_trace_dualLiftToCochain_eq_zero

set_option autoImplicit false

open IsLocalRing groupCohomology TrivSqZeroExt
open scoped DualNumber
theorem GaloisRepAdic.detIsCyclotomic_iff_forall_trace_dualLiftToCochain_eq_zero
    (k : Type) [Field k] (ρbar : ResidualGaloisRep k)
    (p : ℕ) (hp : (p : k) = 0) (hp0 : 0 < p)
    (hdet : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : ℕ),
      (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) →
      LinearMap.det (ρbar.ρ σ) = (a : k))
    (ρ : GaloisRepAdic (DualNumber k))
    (ρd : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (DualNumber (Module.End k ρbar.V))ˣ)
    (hρd : IsDualLift ρbar.ρ.toHomUnits ρd)
    (b : Module.Basis (Fin 2) (DualNumber k) ρ.V) (bbar : Module.Basis (Fin 2) k ρbar.V)
    (hdict : ∀ σ, LinearMap.toMatrix b b (ρ.ρ σ) =
      Matrix.dualNumberEquiv.symm
        ⟨LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).fst),
          LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).snd)⟩) :
    ρ.DetIsCyclotomic p ↔
      ∀ σ, LinearMap.trace k ρbar.V (dualLiftToCochain ρbar.ρ.toHomUnits ρd σ) = 0 := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_detIsCyclotomic_iff_forall_trace_dualLiftToCochain_eq_zero.solution
