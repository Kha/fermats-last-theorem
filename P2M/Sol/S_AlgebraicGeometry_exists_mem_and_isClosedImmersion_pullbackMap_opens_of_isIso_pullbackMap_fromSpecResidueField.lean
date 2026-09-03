import Mathlib
import Theorems.Thm_AlgebraicGeometry_isIso_fiberToSpecResidueField_and_exists_isFinite_morphismRestrict_of_isIso_pullbackMap_fromSpecResidueField
import Theorems.Thm_AlgebraicGeometry_exists_mem_and_isClosedImmersion_pullbackMap_opens_of_isFinite_morphismRestrict_of_isIso_fiberToSpecResidueField
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_exists_mem_and_isClosedImmersion_pullbackMap_opens_of_isIso_pullbackMap_fromSpecResidueField

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (q : X ⟶ Y) (h : Z ⟶ X) (w : h ≫ q = p)
    [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    [IsProper q] [Flat q] [LocallyOfFinitePresentation q]
    (y : Y) (hy : IsIso (pullback.map p (Y.fromSpecResidueField y) q (Y.fromSpecResidueField y) h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp]))) :
    ∃ V : Y.Opens, y ∈ V ∧
      IsClosedImmersion (pullback.map p V.ι q V.ι h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp])) := by
  obtain ⟨hfib, V₀, hy₀, hfin⟩ :=
    AlgebraicGeometry.isIso_fiberToSpecResidueField_and_exists_isFinite_morphismRestrict_of_isIso_pullbackMap_fromSpecResidueField p q h w y hy
  exact AlgebraicGeometry.exists_mem_and_isClosedImmersion_pullbackMap_opens_of_isFinite_morphismRestrict_of_isIso_fiberToSpecResidueField p q h w y V₀ hy₀ hfin hfib
