import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import Definitions.Def_AlgebraicGeometry_FppfAmitsurTrivial
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_fppfAmitsurTrivial_gmAbelianSheafLifted
open CategoryTheory AlgebraicGeometry
theorem AlgebraicGeometry.Scheme.fppfAmitsurTrivial_gmAbelianSheafLifted
    (A : Type) [CommRing A] [Module.FaithfullyFlat ℤ A] :
    Scheme.FppfAmitsurTrivial FppfKummerSES.GmAbelianSheafLifted.{0} A := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_fppfAmitsurTrivial_gmAbelianSheafLifted.solution
