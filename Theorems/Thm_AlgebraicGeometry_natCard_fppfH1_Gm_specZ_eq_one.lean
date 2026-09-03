import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_natCard_fppfH1_Gm_specZ_eq_one
attribute [-simp] Algebra.DescentCofaces.i₁_apply Algebra.DescentCofaces.i₂_apply Algebra.DescentCofaces.c₁₂_tmul Algebra.DescentCofaces.c₂₃_tmul Algebra.DescentCofaces.c₁₃_tmul
open CategoryTheory Abelian Limits AlgebraicGeometry
theorem AlgebraicGeometry.natCard_fppfH1_Gm_specZ_eq_one :
    Nat.card (FppfCohomologyLES.FppfH FppfKummerSES.GmAbelianSheafLifted.{0} 1) = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_natCard_fppfH1_Gm_specZ_eq_one.solution
