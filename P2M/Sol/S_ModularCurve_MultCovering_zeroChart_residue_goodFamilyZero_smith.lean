import Definitions.Def_ModularCurve_MultCoveringFamily
import P2M.Util
namespace P2MW.S_ModularCurve_MultCovering_zeroChart_residue_goodFamilyZero_smith

set_option autoImplicit false
set_option Elab.async false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    {r : ℕ} (Φ : FamCtx p r)
    (hw : ∀ e, ssValue Γ e ≠ 0 ∧ ssValue Γ e ≠ 1728) :
    ∃ (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
      (P : Fin r → Polynomial (IsLocalRing.ResidueField ↥A)),
      (∀ l, (P l).natDegree ≤ mAnnuli p) ∧
      LinearIndependent (IsLocalRing.ResidueField ↥A) P ∧
      (∀ Q : Polynomial (IsLocalRing.ResidueField ↥A), Q.natDegree ≤ mAnnuli p →
        Q ∈ Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range P)) ∧
      (∀ l : Fin r, (l : ℕ) = 0 →
        P l = ∏ e : Fin (mAnnuli p), (Polynomial.X - Polynomial.C (ssValue Γ e ^ p))) ∧
      ∀ l, (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩ * ssPolyBarZero Γ
        = Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l) :=
  Φ.t_zeroChart A hA Γ hw
