import Definitions.Def_AlgebraicGeometry_FppfKummerCalculus
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_fppf_natCard_H1_muP_eq_natCard_H0_muP_of_pic_trivial
p2m_open "CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry"
theorem solution (p : ℕ) (hp : p ≠ 0)
    (hH1Gm : Nat.card (FppfCohomologyLES.FppfH FppfKummerSES.GmAbelianSheafLifted.{0} 1) = 1) :
    Nat.card (FppfCohomologyLES.FppfH (FppfKummerSES.muPAbelianSheafLifted.{0} p) 1) =
      Nat.card (FppfCohomologyLES.FppfH (FppfKummerSES.muPAbelianSheafLifted.{0} p) 0) :=
  FppfBigSiteH0Gm.kummer_h1_card_eq_h0_card_of_pic_trivial_specZ p hp hH1Gm
