import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIso_fiberToSpecResidueField_and_exists_isFinite_morphismRestrict_of_isIso_pullbackMap_fromSpecResidueField

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isIso_fiberToSpecResidueField_and_exists_isFinite_morphismRestrict_of_isIso_pullbackMap_fromSpecResidueField
    {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (q : X ⟶ Y) (h : Z ⟶ X) (w : h ≫ q = p)
    [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    [IsProper q] [Flat q] [LocallyOfFinitePresentation q]
    (y : Y) (hy : IsIso (pullback.map p (Y.fromSpecResidueField y) q (Y.fromSpecResidueField y) h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp]))) :
    (∀ x : X, q.base x = y → IsIso (h.fiberToSpecResidueField x)) ∧
      ∃ V : Y.Opens, y ∈ V ∧ IsFinite (h ∣_ (q ⁻¹ᵁ V)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIso_fiberToSpecResidueField_and_exists_isFinite_morphismRestrict_of_isIso_pullbackMap_fromSpecResidueField.solution
