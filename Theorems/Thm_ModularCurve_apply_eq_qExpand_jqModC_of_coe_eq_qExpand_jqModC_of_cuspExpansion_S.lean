import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S
    (M : ℕ) [NeZero M] {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]
    (φ : integralClosure ℤ ℂ →+* K)
    (N d : ℕ) [NeZero N] [NeZero d] (hM : N * d = M)
    (Θ : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) →ₐ[K] LaurentSeries K)
    (hΘ :
      ∀ (k : ℤ) (f h : ModularForm (CohCarrier.GammaH M ⊥ : Subgroup (GL (Fin 2) ℝ)) k)
        (pf ph : PowerSeries ℤ), ModularCurve.IsIntegralQExp f pf →
        ModularCurve.IsIntegralQExp h ph → ModularCurve.intSeriesC K ph ≠ 0 →
        ∀ (a : ℕ) (F G : PowerSeries (integralClosure ℤ ℂ)),
          F.map (algebraMap (integralClosure ℤ ℂ) ℂ) =
            (M : ℂ) ^ a • UpperHalfPlane.qExpansion M ((⇑f : UpperHalfPlane → ℂ) ∣[k] ModularGroup.S) →
          G.map (algebraMap (integralClosure ℤ ℂ) ℂ) =
            (M : ℂ) ^ a • UpperHalfPlane.qExpansion M ((⇑h : UpperHalfPlane → ℂ) ∣[k] ModularGroup.S) →
          ∀ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M ⊥),
            (x : LaurentSeries K) = ModularCurve.intSeriesC K pf / ModularCurve.intSeriesC K ph →
            HahnSeries.ofPowerSeries ℤ K (G.map φ) ≠ 0 ∧
              (Θ x : LaurentSeries K) =
                HahnSeries.ofPowerSeries ℤ K (F.map φ) / HahnSeries.ofPowerSeries ℤ K (G.map φ)) :
    ∀ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M ⊥),
      (x : LaurentSeries K) = ModularCurve.qExpand K d (ModularCurve.jqModC K) →
        (Θ x : LaurentSeries K) = ModularCurve.qExpand K N (ModularCurve.jqModC K) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S.solution
