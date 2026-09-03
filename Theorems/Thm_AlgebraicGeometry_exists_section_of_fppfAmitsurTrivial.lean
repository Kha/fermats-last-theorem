import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import Definitions.Def_AlgebraicGeometry_FppfAmitsurTrivial
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_section_of_fppfAmitsurTrivial

set_option autoImplicit false

open CategoryTheory Opposite AlgebraicGeometry

theorem AlgebraicGeometry.exists_section_of_fppfAmitsurTrivial
    (F E : Sheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}) (f : F ⟶ E)
    (g : E ⟶ (constantSheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}).obj (.of (ULift.{1} ℤ)))
    (w : f ≫ g = 0) (hS : (ShortComplex.mk f g w).ShortExact)
    (H : ∀ (A : Type) [CommRing A] [Module.FaithfullyFlat ℤ A] [Algebra.FinitePresentation ℤ A],
      Scheme.FppfAmitsurTrivial F A) :
    ∃ s : (constantSheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}).obj (.of (ULift.{1} ℤ)) ⟶ E,
      s ≫ g = 𝟙 _ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_section_of_fppfAmitsurTrivial.solution
