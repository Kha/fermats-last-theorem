import Theorems.Thm_AlgebraicGeometry_fppf_extClass_surjective
import Theorems.Thm_AlgebraicGeometry_fppf_extClass_Gm_eq_zero
import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_subsingleton_fppfH1_Gm_specZ
attribute [-simp] Algebra.DescentCofaces.i₁_apply Algebra.DescentCofaces.i₂_apply Algebra.DescentCofaces.c₁₂_tmul Algebra.DescentCofaces.c₂₃_tmul Algebra.DescentCofaces.c₁₃_tmul

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry"

theorem solution :
    Subsingleton (FppfCohomologyLES.FppfH FppfKummerSES.GmAbelianSheafLifted.{0} 1) := by
  suffices h0 : ∀ c : FppfCohomologyLES.FppfH FppfKummerSES.GmAbelianSheafLifted.{0} 1, c = 0 from
    ⟨fun a b => (h0 a).trans (h0 b).symm⟩
  intro c
  obtain ⟨E, f, g, w, hS, heq⟩ :=
    AlgebraicGeometry.fppf_extClass_surjective FppfKummerSES.GmAbelianSheafLifted.{0} c
  rw [← heq]
  exact AlgebraicGeometry.fppf_extClass_Gm_eq_zero E f g w hS
