import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import P2M.Util
import P2M.Sol.S_ModularCurve_diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply
attribute [-simp] ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply

set_option autoImplicit false

open scoped MatrixGroups ModularForm
open CongruenceSubgroup open ModularCurve hiding exists_algEquiv_laurentBaseChange_cover exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0

theorem ModularCurve.diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (ρ : Gamma0 M →* RingAut ↥(xHFunctionField M H))
    (hρH : ∀ γ : Gamma0 M, (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H → ρ γ = 1)
    (hρslash : ∀ (γ : Gamma0 M) {k : ℤ}
      (f g f₁ g₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
      {pf pg pf₁ pg₁ : PowerSeries ℤ} (c : ℂ) (_ : c ≠ 0)
      (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
      (_ : IsIntegralQExp f₁ pf₁) (_ : IsIntegralQExp g₁ pg₁)
      (_ : (⇑f₁ : UpperHalfPlane → ℂ) = c • ((⇑f : UpperHalfPlane → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)))
      (_ : (⇑g₁ : UpperHalfPlane → ℂ) = c • ((⇑g : UpperHalfPlane → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)))
      (hg0 : intSeriesC ℚ pg ≠ 0) (_ : intSeriesC ℚ pg₁ ≠ 0),
      ((ρ γ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ : ↥(xHFunctionField M H)) :
          LaurentSeries ℚ) = intSeriesC ℚ pf₁ / intSeriesC ℚ pg₁)
    (d : (ZMod M)ˣ) (γ : Gamma0 M) (hγ : (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = (d : ZMod M))
    (x : ↥(xHFunctionField M H)) :
    ((diamondAutHBar M H d ⟨coeffEmb (AlgebraicClosure ℚ) (x : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) x.2⟩ : ↥(xHFunctionFieldBar M H)) :
        LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) ((ρ γ x : ↥(xHFunctionField M H)) : LaurentSeries ℚ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply.solution
