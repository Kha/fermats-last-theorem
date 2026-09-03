import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem ModularCurve.exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H) :
    ∃ w : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)) ≃ₐ[AlgebraicClosure ℚ]
        ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)),
      (∀ x : ModularCurve.xHFunctionFieldBar M H,
          w (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ x) =
            ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ x) ∧
      (∀ x : ModularCurve.xHFunctionFieldBar M H,
          w (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ x) =
            ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ
              (ModularCurve.diamondAutHBar M H
                (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM)) x)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar.solution
