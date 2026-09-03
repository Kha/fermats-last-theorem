import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_fppf_extClass_Gm_eq_zero
attribute [-simp] Algebra.DescentCofaces.i₁_apply Algebra.DescentCofaces.i₂_apply Algebra.DescentCofaces.c₁₂_tmul Algebra.DescentCofaces.c₂₃_tmul Algebra.DescentCofaces.c₁₃_tmul
open CategoryTheory Abelian Limits AlgebraicGeometry
theorem AlgebraicGeometry.fppf_extClass_Gm_eq_zero
    (E : CategoryTheory.Sheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1})
    (f : FppfKummerSES.GmAbelianSheafLifted.{0} ⟶ E)
    (g : E ⟶ (CategoryTheory.constantSheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}).obj (.of (ULift.{1} ℤ)))
    (w : f ≫ g = 0)
    (hS : (CategoryTheory.ShortComplex.mk f g w).ShortExact) :
    hS.extClass = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_fppf_extClass_Gm_eq_zero.solution
