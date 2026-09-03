import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_forall_ord_residue_pos_of_maximalIdeal_le_map_sup_span

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.forall_ord_residue_pos_of_maximalIdeal_le_map_sup_span
    {L : Type*} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar) (x : Place (ResidueField A) Fbar)
    (N₀ N₁ : Subring F) [IsLocalRing ↥N₀] [IsLocalRing ↥N₁] (h01 : N₀ ≤ N₁)
    (hN₁ : ∀ f : F, f ∈ N₁ → f ∈ R.integers)
    (hreg₀ : ∀ (f : ↥N₀) (h : (f : F) ∈ R.integers), 0 ≤ x.ord (R.residue ⟨f, h⟩) ∧
      (¬ IsUnit f → R.residue ⟨f, h⟩ ≠ 0 → 0 < x.ord (R.residue ⟨f, h⟩)))
    (hreg₁ : ∀ (f : ↥N₁) (h : (f : F) ∈ R.integers), 0 ≤ x.ord (R.residue ⟨f, h⟩))
    (w : F) (hw : w ∈ N₁) (hwres : ∀ h : w ∈ R.integers, R.residue ⟨w, h⟩ = 0)
    (hmax : maximalIdeal ↥N₁ ≤ (maximalIdeal ↥N₀).map (Subring.inclusion h01) ⊔ Ideal.span {⟨w, hw⟩}) :
    ∀ (f : ↥N₁) (h : (f : F) ∈ R.integers), 0 ≤ x.ord (R.residue ⟨f, h⟩) ∧
      (¬ IsUnit f → R.residue ⟨f, h⟩ ≠ 0 → 0 < x.ord (R.residue ⟨f, h⟩)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_forall_ord_residue_pos_of_maximalIdeal_le_map_sup_span.solution
