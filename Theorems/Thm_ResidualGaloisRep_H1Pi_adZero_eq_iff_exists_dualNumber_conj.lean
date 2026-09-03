import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_H1Pi_adZero_eq_iff_exists_dualNumber_conj

set_option autoImplicit false

open IsLocalRing groupCohomology TrivSqZeroExt
open scoped DualNumber
theorem ResidualGaloisRep.H1Pi_adZero_eq_iff_exists_dualNumber_conj
    (k : Type) [Field k] (ρbar : ResidualGaloisRep k) (h2 : IsUnit (2 : k))
    (ρ ρ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (DualNumber (Module.End k ρbar.V))ˣ)
    (hρ : IsDualLift ρbar.ρ.toHomUnits ρ) (hρ' : IsDualLift ρbar.ρ.toHomUnits ρ')
    (c c' : cocycles₁ ρbar.adZero)
    (hc : ∀ σ, ((c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
        ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) σ : Module.End k ρbar.V) =
      dualLiftToCochain ρbar.ρ.toHomUnits ρ σ)
    (hc' : ∀ σ, ((c' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
        ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) σ : Module.End k ρbar.V) =
      dualLiftToCochain ρbar.ρ.toHomUnits ρ' σ) :
    H1π ρbar.adZero c = H1π ρbar.adZero c' ↔
      ∃ w : (DualNumber (Module.End k ρbar.V))ˣ,
        (w : DualNumber (Module.End k ρbar.V)).fst = 1 ∧ ∀ σ, ρ' σ = w * ρ σ * w⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_H1Pi_adZero_eq_iff_exists_dualNumber_conj.solution
