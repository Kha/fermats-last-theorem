import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import P2M.Util
import P2M.Sol.S_ModularCurve_MultCovering_ord_nodeSrc_zeroChart_residue_sub_algebraMap_eq_one_of_digits
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering

theorem ModularCurve.MultCovering.ord_nodeSrc_zeroChart_residue_sub_algebraMap_eq_one_of_digits
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
    (e : Fin (mAnnuli p)) (he : jWidth (ssValue Γ e) = 3)

    (a w : Fin r → ResidueField ↥A)
    (ha : ∀ j : Fin r, hasseExp Φ.toFamData j ≤ 1 →
      (nodeSrc Γ e).HasValue ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j, hint j⟩) (a j))
    (hw : ∀ j : Fin r, hasseExp Φ.toFamData j ≤ 1 →
      (nodeSrc Γ e).HasValue
        (((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j, hint j⟩
            - algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1) (a j))
          * ((⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) 1⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) 1))
              - algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1) (ssValue Γ e ^ p))⁻¹)
        (w j))

    (hunr : ∀ i : Fin r, 1 ≤ (i : ℕ) → hasseExp Φ.toFamData i = 1 →
      (∑ j : Fin r, (if hasseExp Φ.toFamData j ≤ hasseExp Φ.toFamData i then ((d i j).val : ResidueField ↥A) else 0)
        * w j) ≠ 0) :
    ∀ i : Fin r, 1 ≤ (i : ℕ) → hasseExp Φ.toFamData i = 1 →
      ∃ c : ResidueField ↥A,
        (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨g' i, hint' i⟩
          - algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1) c) = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_MultCovering_ord_nodeSrc_zeroChart_residue_sub_algebraMap_eq_one_of_digits.solution
