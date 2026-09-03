import Definitions.Def_AlgebraicGeometry_FppfKummerCalculus
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_fppf_natCard_H1_muP_eq_one_of_odd_of_pic_trivial
p2m_open "CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry"
theorem solution (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hH1Gm : Nat.card (FppfCohomologyLES.FppfH FppfKummerSES.GmAbelianSheafLifted.{0} 1) = 1) :
    Nat.card (FppfCohomologyLES.FppfH (FppfKummerSES.muPAbelianSheafLifted.{0} p) 1) = 1 := by
  have hne : p ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hodd
    omega
  have h := FppfBigSiteH0Gm.kummer_h1_card_value_of_pic_trivial p hp hH1Gm
  rw [if_neg hne] at h
  exact h
