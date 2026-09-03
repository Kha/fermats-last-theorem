import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_coe_eq_correspondence_and_mk_eq_genOpH_U_mk_and_smul_norm_ne_zero_and_forall_mul_smul_eq_ord

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_coe_eq_correspondence_and_mk_eq_genOpH_U_mk_and_smul_norm_ne_zero_and_forall_mul_smul_eq_ord
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (hin : HeckeDiamondInputsHAll M H)
    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (D : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
    (f : ↥(xHFunctionFieldBar M H)) (hf : f ≠ 0)
    (hdivf : ∀ v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      (p : ℤ) * (wgen • (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) v = v.ord f) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∃ (hα : HeckeAlphaHBarIntegral (AlgebraicClosure ℚ) M H p) (hβ : HeckeBetaHBarIntegral (AlgebraicClosure ℚ) M H p)
      (_ : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * p))))
      (hfin : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaHBar (AlgebraicClosure ℚ) M H p))
      (_ : NormFormulaAlong (AlgebraicClosure ℚ) (heckeAlphaHBar (AlgebraicClosure ℚ) M H p) hfin)
      (D_U : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
      (D_U : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Divisor.correspondence (heckeBetaHBar (AlgebraicClosure ℚ) M H p) (heckeAlphaHBar (AlgebraicClosure ℚ) M H p) hβ hα
            (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∧
      (Pic0.mk D_U : JH M H) = genOpH M H S (CohCarrier.Gen.U p Fact.out hpM) (Pic0.mk D) ∧
      (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H p)
       wgen • (Algebra.norm ↥(xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H p (wgen⁻¹ • f)) : ↥(xHFunctionFieldBar M H)) ≠ 0) ∧
      ∀ v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        (p : ℤ) * (wgen • (D_U : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) v =
          v.ord (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H p)
                 wgen • (Algebra.norm ↥(xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H p (wgen⁻¹ • f)) : ↥(xHFunctionFieldBar M H))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_coe_eq_correspondence_and_mk_eq_genOpH_U_mk_and_smul_norm_ne_zero_and_forall_mul_smul_eq_ord.solution
