import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_Place_module_finite_residueField_restrict
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Divisor_pushforwardAlong_single_one_of_isAlgClosed

set_option autoImplicit false

open AlgebraicCurve in
theorem solution
    {K F F' : Type*} [Field K] [IsAlgClosed K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [AlgebraicCurve.IsCurveOver K F]
    (ψ : F →ₐ[K] F') (hψ : ψ.toRingHom.IsIntegral) (hfin : AlgebraicCurve.FiniteAlong K ψ)
    (W : AlgebraicCurve.Place K F') :
    AlgebraicCurve.Divisor.pushforwardAlong ψ hψ (Finsupp.single W 1) =
      Finsupp.single (W.restrictAlong ψ hψ) 1 := by
  letI := algebraAlong ψ
  haveI := isScalarTower_along ψ
  haveI := isIntegral_along ψ hψ
  haveI : Module.Finite F F' := hfin
  haveI := AlgebraicCurve.Place.module_finite_residueField_restrict K F F' W
  haveI := IsCurveOver.finiteResidue (K := K) (W.restrict F)
  haveI : Module.Finite K W.ResidueField := Module.Finite.trans (W.restrict F).ResidueField _
  have hW : W.deg = 1 := W.deg_eq_one_of_isAlgClosed_of_finite
  have hV : (W.restrictAlong ψ hψ).deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed _
  have h1 : W.inertiaDegAlong ψ hψ = 1 := by
    have ht : (W.restrictAlong ψ hψ).deg * W.inertiaDegAlong ψ hψ = W.deg :=
      W.deg_restrict_mul_inertiaDeg (F := F)
    rw [hV, hW, one_mul] at ht
    exact ht
  rw [Divisor.pushforwardAlong_single, h1, Nat.cast_one, mul_one]
