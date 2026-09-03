import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import P2M.Util
import P2M.Sol.S_ModularCurve_MultCovering_FamData_linearIndependent_zeroChart_residue_goodFamilyZero

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.FamData.linearIndependent_zeroChart_residue_goodFamilyZero
    (p : ℕ) [Fact p.Prime] {r : ℕ} (D : FamData p r)
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) :
          ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    (hint : ∀ l, goodFamilyZero D l ∈ (zeroChart Γ).integers) :
    LinearIndependent (IsLocalRing.ResidueField ↥A)
      (fun l => (zeroChart Γ).residue ⟨goodFamilyZero D l, hint l⟩) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_MultCovering_FamData_linearIndependent_zeroChart_residue_goodFamilyZero.solution
