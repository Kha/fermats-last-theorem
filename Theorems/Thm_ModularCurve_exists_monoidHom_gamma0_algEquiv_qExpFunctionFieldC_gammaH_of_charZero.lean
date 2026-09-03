import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero
    (K : Type*) [Field K] [CharZero K] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    ∃ ρ : CongruenceSubgroup.Gamma0 M →*
        (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K]
          ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)),
      (∀ γ : CongruenceSubgroup.Gamma0 M, (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H → ρ γ = 1) ∧
      (∀ γ : CongruenceSubgroup.Gamma0 M, (γ : SL(2, ℤ)) = -1 → ρ γ = 1) ∧
      (∀ (γ : CongruenceSubgroup.Gamma0 M) (x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)),
        (x : LaurentSeries K) ∈ ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M) →
          ρ γ x = x) ∧
      (∀ (γ : CongruenceSubgroup.Gamma0 M) {k : ℤ}
        (f g f₁ g₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
        {pf pg pf₁ pg₁ : PowerSeries ℤ} (c : ℂ) (_ : c ≠ 0)
        (hf : ModularCurve.IsIntegralQExp f pf) (hg : ModularCurve.IsIntegralQExp g pg)
        (_ : ModularCurve.IsIntegralQExp f₁ pf₁) (_ : ModularCurve.IsIntegralQExp g₁ pg₁)
        (_ : (⇑f₁ : UpperHalfPlane → ℂ) =
          c • ((⇑f : UpperHalfPlane → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)))
        (_ : (⇑g₁ : UpperHalfPlane → ℂ) =
          c • ((⇑g : UpperHalfPlane → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)))
        (hg0 : ModularCurve.intSeriesC K pg ≠ 0) (_ : ModularCurve.intSeriesC K pg₁ ≠ 0),
          ((ρ γ ⟨ModularCurve.intSeriesC K pf / ModularCurve.intSeriesC K pg,
              ModularCurve.div_mem_qExpFunctionFieldC f g hf hg hg0⟩ :
                ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)) : LaurentSeries K) =
            ModularCurve.intSeriesC K pf₁ / ModularCurve.intSeriesC K pg₁) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero.solution
