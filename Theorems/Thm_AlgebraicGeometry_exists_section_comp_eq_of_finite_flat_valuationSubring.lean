import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_section_comp_eq_of_finite_flat_valuationSubring

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_section_comp_eq_of_finite_flat_valuationSubring
    {L : Type} [Field L] [IsAlgClosed L] (O : ValuationSubring L)
    {Z : Scheme.{0}} (f : Z ⟶ Spec (CommRingCat.of ↥O)) [IsFinite f] [Flat f]
    (zbar : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥O)) ⟶ Z)
    (hzbar : zbar ≫ f = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))) :
    ∃ z : Spec (CommRingCat.of ↥O) ⟶ Z, z ≫ f = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)) ≫ z = zbar := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_section_comp_eq_of_finite_flat_valuationSubring.solution
