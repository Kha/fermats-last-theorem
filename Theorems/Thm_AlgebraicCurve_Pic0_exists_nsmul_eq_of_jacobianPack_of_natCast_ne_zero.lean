import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Pic0_exists_nsmul_eq_of_jacobianPack_of_natCast_ne_zero

open AlgebraicCurve CategoryTheory

theorem AlgebraicCurve.Pic0.exists_nsmul_eq_of_jacobianPack_of_natCast_ne_zero
    (K F : Type*) [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F]
    (J : AlgebraicGeometry.Scheme)
    (c : J ⟶ AlgebraicGeometry.Spec (CommRingCat.of K))
    (hsm : AlgebraicGeometry.Smooth c)
    (hpr : AlgebraicGeometry.IsProper c)
    (hconn : ConnectedSpace J)
    (mul : CategoryTheory.Limits.pullback c c ⟶ J)
    (pts : Pic0 K F ≃
      {σ : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ J // σ ≫ c = 𝟙 _})
    (hadd : ∀ x y : Pic0 K F, (pts (x + y)).1 =
      CategoryTheory.Limits.pullback.lift (pts x).1 (pts y).1
        ((pts x).2.trans (pts y).2.symm) ≫ mul)
    (n : ℕ) (hn : n ≠ 0) (hchar : (n : K) ≠ 0) (x : Pic0 K F) :
    ∃ y : Pic0 K F, n • y = x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Pic0_exists_nsmul_eq_of_jacobianPack_of_natCast_ne_zero.solution
