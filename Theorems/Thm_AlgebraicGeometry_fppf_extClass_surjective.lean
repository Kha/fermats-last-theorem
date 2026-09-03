import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_fppf_extClass_surjective
open CategoryTheory Abelian Limits AlgebraicGeometry
theorem AlgebraicGeometry.fppf_extClass_surjective
    (F : CategoryTheory.Sheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1})
    (e : CategoryTheory.Abelian.Ext
      ((CategoryTheory.constantSheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}).obj
        (.of (ULift.{1} ℤ))) F 1) :
    ∃ (E : CategoryTheory.Sheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1})
      (f : F ⟶ E)
      (g : E ⟶ (CategoryTheory.constantSheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}).obj
        (.of (ULift.{1} ℤ)))
      (w : f ≫ g = 0)
      (hS : (CategoryTheory.ShortComplex.mk f g w).ShortExact),
      hS.extClass = e := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_fppf_extClass_surjective.solution
