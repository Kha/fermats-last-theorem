import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import P2M.Util
import P2M.Sol.S_ModularCurve_XHDRLevel_exists_valuationSubring_gauss_qExpFunctionFieldC

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRLevel.exists_valuationSubring_gauss_qExpFunctionFieldC
    (p : ℕ) [Fact p.Prime] (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    ∃ W₀ : ValuationSubring ↥(qExpFunctionFieldC ℚ Γ),

      (∀ f : ↥(qExpFunctionFieldC ℚ Γ), f ∈ W₀ ↔
        ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
        (f : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
          HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype)) ∧

      (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) a ∈ W₀) ∧
      (∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))},
        algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) a ∈ W₀.nonunits) ∧

      (∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
        Polynomial.aeval (jAt Γ hj) Q ∈ W₀ ∧ (Polynomial.aeval (jAt Γ hj) Q)⁻¹ ∈ W₀) ∧

      (∀ x : ↥(qExpFunctionFieldC ℚ Γ), x ∈ W₀.nonunits →
        x * (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ)
          ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))⁻¹ ∈ W₀) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XHDRLevel_exists_valuationSubring_gauss_qExpFunctionFieldC.solution
