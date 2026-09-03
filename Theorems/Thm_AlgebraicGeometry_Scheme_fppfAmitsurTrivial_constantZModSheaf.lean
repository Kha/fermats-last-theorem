import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import Definitions.Def_AlgebraicGeometry_FppfAmitsurTrivial
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_fppfAmitsurTrivial_constantZModSheaf
open CategoryTheory AlgebraicGeometry
theorem AlgebraicGeometry.Scheme.fppfAmitsurTrivial_constantZModSheaf
    (p : ℕ) (hp : p ≠ 0) (A : Type) [CommRing A] [Module.FaithfullyFlat ℤ A] :
    Scheme.FppfAmitsurTrivial
      (FppfKummerSES.sheafULift.{0}.obj (FppfRepresentableGroupSchemeSheaf.constantZModSheaf.{0} p)) A := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_fppfAmitsurTrivial_constantZModSheaf.solution
