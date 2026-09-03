import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_coe_eq_correspondence_and_mk_eq_heckeOperatorHAlong_mk_and_smul_norm_ne_zero_and_forall_mul_smul_eq_ord

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_coe_eq_correspondence_and_mk_eq_heckeOperatorHAlong_mk_and_smul_norm_ne_zero_and_forall_mul_smul_eq_ord
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hin : HeckeDiamondInputsHAll M H)
    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (D : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
    (f : ↥(xHFunctionFieldBar M H)) (hf : f ≠ 0)
    (hdivf : ∀ v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      (p : ℤ) * (wgen • (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) v = v.ord f) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ∃ (hα : HeckeAlphaHBarIntegral (AlgebraicClosure ℚ) M H ℓ) (hβ : HeckeBetaHBarIntegral (AlgebraicClosure ℚ) M H ℓ)
      (_ : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * ℓ))))
      (hfin : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ))
      (_ : NormFormulaAlong (AlgebraicClosure ℚ) (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) hfin)
      (D_ℓ : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
      (D_ℓ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Divisor.correspondence (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ) (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) hβ hα
            (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∧
      (Pic0.mk D_ℓ : JH M H) = heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ (Pic0.mk D) ∧
      (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ)
       wgen • (Algebra.norm ↥(xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ (wgen⁻¹ • f)) : ↥(xHFunctionFieldBar M H)) ≠ 0) ∧
      ∀ v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        (p : ℤ) * (wgen • (D_ℓ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) v =
          v.ord (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ)
                 wgen • (Algebra.norm ↥(xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ (wgen⁻¹ • f)) : ↥(xHFunctionFieldBar M H))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_coe_eq_correspondence_and_mk_eq_heckeOperatorHAlong_mk_and_smul_norm_ne_zero_and_forall_mul_smul_eq_ord.solution
