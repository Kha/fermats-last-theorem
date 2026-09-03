import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import Definitions.Def_AlgebraicGeometry_FppfAmitsurTrivial
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Theorems.Thm_CategoryTheory_ShortComplex_ShortExact_extClass_eq_zero_iff_exists_section_g
import Theorems.Thm_AlgebraicGeometry_exists_section_of_fppfAmitsurTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_fppfAmitsurTrivial_gmAbelianSheafLifted
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_fppf_extClass_Gm_eq_zero
set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry"

theorem solution
    (E : CategoryTheory.Sheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1})
    (f : FppfKummerSES.GmAbelianSheafLifted.{0} ⟶ E)
    (g : E ⟶ (CategoryTheory.constantSheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}).obj (.of (ULift.{1} ℤ)))
    (w : f ≫ g = 0)
    (hS : (CategoryTheory.ShortComplex.mk f g w).ShortExact) :
    hS.extClass = 0 := by
  rw [hS.extClass_eq_zero_iff_exists_section_g]
  exact AlgebraicGeometry.exists_section_of_fppfAmitsurTrivial _ E f g w hS
    (fun A _ _ _ => AlgebraicGeometry.Scheme.fppfAmitsurTrivial_gmAbelianSheafLifted A)
