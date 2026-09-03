import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDifferentialsModL
import P2M.Util
import P2M.Sol.S_ModularCurve_coe_ringAut_gamma0_apply_eq_of_coe_eq_infSubgroup
attribute [-simp] ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply

set_option autoImplicit false

open scoped MatrixGroups
open ModularCurve

open scoped ModularForm in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.coe_ringAut_gamma0_apply_eq_of_coe_eq_infSubgroup
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (ρM : CongruenceSubgroup.Gamma0 M →* RingAut ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hρM_H : ∀ γ : CongruenceSubgroup.Gamma0 M, (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H → ρM γ = 1)
    (hρM_slash : (∀ (γ : CongruenceSubgroup.Gamma0 M) {k : ℤ}
      (f g f₁ g₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
      {pf pg pf₁ pg₁ : PowerSeries ℤ} (c : ℂ) (_ : c ≠ 0)
      (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
      (_ : IsIntegralQExp f₁ pf₁) (_ : IsIntegralQExp g₁ pg₁)
      (_ : (⇑f₁ : UpperHalfPlane → ℂ) = c • ((⇑f : UpperHalfPlane → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)))
      (_ : (⇑g₁ : UpperHalfPlane → ℂ) = c • ((⇑g : UpperHalfPlane → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)))
      (hg0 : intSeriesC ℚ pg ≠ 0) (_ : intSeriesC ℚ pg₁ ≠ 0),
      ((ρM γ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ :
          ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) = intSeriesC ℚ pf₁ / intSeriesC ℚ pg₁))
    (ρN : CongruenceSubgroup.Gamma0 (M / p) →*
      RingAut ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))))
    (hρN_H : ∀ γ : CongruenceSubgroup.Gamma0 (M / p),
      (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) → ρN γ = 1)
    (hρN_slash : (∀ (γ : CongruenceSubgroup.Gamma0 (M / p)) {k : ℤ}
      (f g f₁ g₁ : ModularForm (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) : Subgroup (GL (Fin 2) ℝ)) k)
      {pf pg pf₁ pg₁ : PowerSeries ℤ} (c : ℂ) (_ : c ≠ 0)
      (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
      (_ : IsIntegralQExp f₁ pf₁) (_ : IsIntegralQExp g₁ pg₁)
      (_ : (⇑f₁ : UpperHalfPlane → ℂ) = c • ((⇑f : UpperHalfPlane → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)))
      (_ : (⇑g₁ : UpperHalfPlane → ℂ) = c • ((⇑g : UpperHalfPlane → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)))
      (hg0 : intSeriesC ℚ pg ≠ 0) (_ : intSeriesC ℚ pg₁ ≠ 0),
      ((ρN γ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ :
          ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) : LaurentSeries ℚ) = intSeriesC ℚ pf₁ / intSeriesC ℚ pg₁))
    (γ : CongruenceSubgroup.Gamma0 M) (γ' : CongruenceSubgroup.Gamma0 (M / p)) (hγ : (γ : SL(2, ℤ)) = (γ' : SL(2, ℤ)))
    (f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (u : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))))
    (hfu : (f : LaurentSeries ℚ) = (u : LaurentSeries ℚ)) :
    ((ρM γ f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) =
      ((ρN γ' u : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) : LaurentSeries ℚ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coe_ringAut_gamma0_apply_eq_of_coe_eq_infSubgroup.solution
