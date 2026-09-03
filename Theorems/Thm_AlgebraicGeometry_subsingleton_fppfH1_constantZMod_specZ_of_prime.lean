import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_subsingleton_fppfH1_constantZMod_specZ_of_prime
attribute [-simp] Algebra.DescentCofaces.i₁_apply Algebra.DescentCofaces.i₂_apply Algebra.DescentCofaces.c₁₂_tmul Algebra.DescentCofaces.c₂₃_tmul Algebra.DescentCofaces.c₁₃_tmul
open CategoryTheory Abelian Limits AlgebraicGeometry
theorem AlgebraicGeometry.subsingleton_fppfH1_constantZMod_specZ_of_prime (p : ℕ) [Fact p.Prime] :
    Subsingleton (FppfCohomologyLES.FppfH
      (FppfKummerSES.sheafULift.{0}.obj
        (FppfRepresentableGroupSchemeSheaf.constantZModSheaf.{0} p)) 1) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_subsingleton_fppfH1_constantZMod_specZ_of_prime.solution
