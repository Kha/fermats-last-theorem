import Definitions.Def_AlgebraicGeometry_FppfKummerCalculus
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_fppf_natCard_H1_muP_eq_one_of_odd_of_pic_trivial
open CategoryTheory Abelian Limits AlgebraicGeometry
open FppfCohomologyLES FppfKummerSES FppfRepresentableGroupSchemeSheaf FppfBigSiteH0Gm
theorem AlgebraicGeometry.fppf_natCard_H1_muP_eq_one_of_odd_of_pic_trivial
    (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hH1Gm : Nat.card (FppfCohomologyLES.FppfH FppfKummerSES.GmAbelianSheafLifted.{0} 1) = 1) :
    Nat.card (FppfCohomologyLES.FppfH (FppfKummerSES.muPAbelianSheafLifted.{0} p) 1) = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_fppf_natCard_H1_muP_eq_one_of_odd_of_pic_trivial.solution
