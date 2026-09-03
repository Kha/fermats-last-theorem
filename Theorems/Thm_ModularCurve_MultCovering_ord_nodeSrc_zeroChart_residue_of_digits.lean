import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import P2M.Util
import P2M.Sol.S_ModularCurve_MultCovering_ord_nodeSrc_zeroChart_residue_of_digits
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering

theorem ModularCurve.MultCovering.ord_nodeSrc_zeroChart_residue_of_digits
    (p : ℕ) [Fact p.Prime] (hp13 : 13 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r)
    (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (d : Fin r → Fin r → ZMod p)
    (g' : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hint' : ∀ l, g' l ∈ (zeroChart Γ).integers)
    (hres0 : ∀ i : Fin r, (zeroChart Γ).residue ⟨g' i, hint' i⟩
      = ∑ j : Fin r, algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)
          (if hasseExp Φ.toFamData j ≤ hasseExp Φ.toFamData i then ((d i j).val : ResidueField ↥A) else 0)
          * (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j, hint j⟩)

    (hreg : ∀ (e : Fin (mAnnuli p)) (j : Fin r), hasseExp Φ.toFamData j < jWidth (ssValue Γ e) →
      (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j, hint j⟩ ∈ (nodeSrc Γ e).toValuationSubring)

    (hz : ∀ (e : Fin (mAnnuli p)) (i : Fin r), jWidth (ssValue Γ e) ≠ 1 → hasseExp Φ.toFamData i < jWidth (ssValue Γ e) →
      (∑ j : Fin r, (if hasseExp Φ.toFamData j ≤ hasseExp Φ.toFamData i then ((d i j).val : ResidueField ↥A) else 0)
        * (nodeSrc Γ e).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j, hint j⟩)) ≠ 0)
    (hsep : ∀ (e e' : Fin (mAnnuli p)) (i : Fin r), e ≠ e' → jWidth (ssValue Γ e) ≠ 1 → jWidth (ssValue Γ e') ≠ 1 →
      1 ≤ (i : ℕ) → hasseExp Φ.toFamData i = 1 →
      (∑ j : Fin r, (if hasseExp Φ.toFamData j ≤ hasseExp Φ.toFamData i then ((d i j).val : ResidueField ↥A) else 0)
        * ((nodeSrc Γ e).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j, hint j⟩)
           - (nodeSrc Γ e').evalAt ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j, hint j⟩))) ≠ 0) :
    (∀ (e : Fin (mAnnuli p)) (i : Fin r), jWidth (ssValue Γ e) ≠ 1 → hasseExp Φ.toFamData i < jWidth (ssValue Γ e) →
      (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨g' i, hint' i⟩) = 0) ∧
    (∀ (e e' : Fin (mAnnuli p)) (i : Fin r), e ≠ e' → jWidth (ssValue Γ e) ≠ 1 → jWidth (ssValue Γ e') ≠ 1 →
      1 ≤ (i : ℕ) → hasseExp Φ.toFamData i = 1 →
      (nodeSrc Γ e).evalAt ((zeroChart Γ).residue ⟨g' i, hint' i⟩)
        ≠ (nodeSrc Γ e').evalAt ((zeroChart Γ).residue ⟨g' i, hint' i⟩)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_MultCovering_ord_nodeSrc_zeroChart_residue_of_digits.solution
