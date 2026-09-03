import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import P2M.Util
import P2M.Sol.S_CuspForm_exists_isIntegralQExp_congr_and_qExpansion_slash_fricke_congr_of_mem_twoCuspIntegralSet
attribute [-simp] PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.exists_isIntegralQExp_congr_and_qExpansion_slash_fricke_congr_of_mem_twoCuspIntegralSet
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (𝔪 : Ideal ↥(integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsPrime)
    (hp𝔪 : ((p : ℕ) : ↥(integralClosure ℤ ℂ)) ∈ 𝔪)
    (Wd : ModularForm.AtkinLehnerDatum M (M / p))
    (e : (ZMod M)ˣ) (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)
    (WQ : GL (Fin 2) ℝ) (hWQ : (WQ : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; ((M / p : ℕ) : ℝ), 0])
    (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (pf : PowerSeries ℤ) (hpf : ModularCurve.IsIntegralQExp ⇑f pf)
    (D : ℕ) (hD : ¬ p ∣ D)
    (pfW : PowerSeries ↥(integralClosure ℤ ℂ))
    (hpfW : pfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
      UpperHalfPlane.qExpansion 1 ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f))) :
    ∃ (w : ℕ) (G : ModularForm (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) : Subgroup (GL (Fin 2) ℝ)) ((2 : ℤ) + w))
      (P : PowerSeries ℤ) (D₁ D₂ : ℕ) (PGW : PowerSeries ↥(integralClosure ℤ ℂ)),
      0 < w ∧ (p - 1 ∣ w) ∧ (4 ∣ w) ∧ ¬ p ∣ D₁ ∧ ¬ p ∣ D₂ ∧
      ModularCurve.IsIntegralQExp ⇑G P ∧
      (∀ n : ℕ, (p : ℤ) ∣ PowerSeries.coeff n P - (D₁ : ℤ) * PowerSeries.coeff n pf) ∧
      PGW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
        UpperHalfPlane.qExpansion 1 ((D₂ : ℂ) • ((⇑G : UpperHalfPlane → ℂ) ∣[(2 : ℤ) + w] WQ)) ∧
      (∀ n : ℕ, ((D : ℕ) : ↥(integralClosure ℤ ℂ)) * PowerSeries.coeff n PGW -
          ((D₂ * D₁ * (M / p) ^ w : ℕ) : ↥(integralClosure ℤ ℂ)) * PowerSeries.coeff n pfW ∈ 𝔪) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_isIntegralQExp_congr_and_qExpansion_slash_fricke_congr_of_mem_twoCuspIntegralSet.solution
