import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_mem_nonunit_ord_residue_eq_zero_of_ne_centre

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.exists_mem_nonunit_ord_residue_eq_zero_of_ne_centre
    {L : Type} [Field L] (A : ValuationSubring L) {F : Type} [Field F] [Algebra L F]
    {FSS : Type} [Field FSS] [Algebra (ResidueField ↥A) FSS]
    (R : RegularProlongation A F FSS)
    (O : Subring F) [IsLocalRing ↥O] (hOR : ∀ f : F, f ∈ O → f ∈ R.integers)
    (Bx : Subring F) (hBO : Bx ≤ O)
    (hloc : ∀ f : F, f ∈ O ↔ ∃ g h : F, g ∈ Bx ∧ h ∈ Bx ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g)
    (nd y : Place (ResidueField ↥A) FSS)

    (huniq : ∀ y' : Place (ResidueField ↥A) FSS,
      (∀ (b : F) (hb : b ∈ Bx), R.residue ⟨b, hOR b (hBO hb)⟩ ∈ y'.toValuationSubring) →
      (∀ (b : F) (hb : b ∈ Bx), ¬ IsUnit (⟨b, hBO hb⟩ : ↥O) →
        ∃ hm : R.residue ⟨b, hOR b (hBO hb)⟩ ∈ y'.toValuationSubring, (⟨_, hm⟩ : ↥y'.toValuationSubring) ∈ maximalIdeal ↥y'.toValuationSubring) →
      y' = nd)
    (hy : ∀ (b : F) (hb : b ∈ Bx), R.residue ⟨b, hOR b (hBO hb)⟩ ∈ y.toValuationSubring)
    (hne : y ≠ nd) :
    ∃ (g : F) (hg : g ∈ Bx), ¬ IsUnit (⟨g, hBO hg⟩ : ↥O) ∧
      y.ord (R.residue ⟨g, hOR g (hBO hg)⟩) = 0 ∧ R.residue ⟨g, hOR g (hBO hg)⟩ ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_mem_nonunit_ord_residue_eq_zero_of_ne_centre.solution
