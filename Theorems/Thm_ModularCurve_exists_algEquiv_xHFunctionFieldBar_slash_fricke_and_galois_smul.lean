import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul
attribute [-simp] CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply

open scoped MatrixGroups ModularForm

theorem ModularCurve.exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul (M : ℕ)
    [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hin : ∀ d : (ZMod M)ˣ, ∃ σ : ModularCurve.xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ]
      ModularCurve.xHFunctionFieldBar M H, ModularCurve.IsDiamondAutHBar M H d σ)
    (ι : AlgebraicClosure ℚ →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0]) :
    ∃ w : ModularCurve.xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ]
        ModularCurve.xHFunctionFieldBar M H,
      (∀ (x : ModularCurve.xHFunctionFieldBar M H) (k : ℤ)
          (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k),
          ModularCurve.coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) *
              HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) =
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) →
          ModularCurve.coeffMap ι ((w x : ModularCurve.xHFunctionFieldBar M H) :
                LaurentSeries (AlgebraicClosure ℚ)) *
              HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑g ∣[k] W)) =
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f ∣[k] W))) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
          (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
          ∀ x : ModularCurve.xHFunctionFieldBar M H,
            w (ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField M H) σ • x) =
              ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField M H) σ •
                ModularCurve.diamondAutHBar M H (ZMod.unitOfCoprime c hc) (w x)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul.solution
