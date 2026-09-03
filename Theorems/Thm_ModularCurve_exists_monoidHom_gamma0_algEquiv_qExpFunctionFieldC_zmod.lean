import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X0ModL
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_zmod
attribute [-instance] CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply

open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_zmod
    (ℓ : ℕ) [Fact ℓ.Prime] (M : ℕ) [NeZero M] (hℓM : ¬ ℓ ∣ M) (H : Subgroup (ZMod M)ˣ) :
    ∃ ρ : CongruenceSubgroup.Gamma0 M →*
        (ModularCurve.qExpFunctionFieldC (ZMod ℓ) (CohCarrier.GammaH M H) ≃ₐ[ZMod ℓ]
          ModularCurve.qExpFunctionFieldC (ZMod ℓ) (CohCarrier.GammaH M H)),
      (∀ (γ : CongruenceSubgroup.Gamma0 M) (k : ℤ)
          (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k) (p : PowerSeries ℤ),
          ModularCurve.IsIntegralQExp f p →
          ∃ (n : ℕ) (f₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k) (p₁ : PowerSeries ℤ),
            (⇑f₁ : UpperHalfPlane → ℂ) = ((M : ℂ) ^ n) • ((⇑f : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))) ∧
            ModularCurve.IsIntegralQExp f₁ p₁ ∧
            (ModularCurve.intSeriesC (ZMod ℓ) p₁ = 0 ↔ ModularCurve.intSeriesC (ZMod ℓ) p = 0)) ∧
      (∀ (γ : CongruenceSubgroup.Gamma0 M) (k : ℤ)
          (f g f₁ g₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
          (pf pg pf₁ pg₁ : PowerSeries ℤ),
          ModularCurve.IsIntegralQExp f pf → ModularCurve.IsIntegralQExp g pg →
          ModularCurve.IsIntegralQExp f₁ pf₁ → ModularCurve.IsIntegralQExp g₁ pg₁ →
          (⇑f₁ : UpperHalfPlane → ℂ) = ((⇑f : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))) →
          (⇑g₁ : UpperHalfPlane → ℂ) = ((⇑g : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))) →
          ModularCurve.intSeriesC (ZMod ℓ) pg ≠ 0 →
          ∀ x : ModularCurve.qExpFunctionFieldC (ZMod ℓ) (CohCarrier.GammaH M H),
            (x : LaurentSeries (ZMod ℓ)) =
                ModularCurve.intSeriesC (ZMod ℓ) pf₁ / ModularCurve.intSeriesC (ZMod ℓ) pg₁ →
            ((ρ γ x : ModularCurve.qExpFunctionFieldC (ZMod ℓ) (CohCarrier.GammaH M H)) :
                LaurentSeries (ZMod ℓ)) =
              ModularCurve.intSeriesC (ZMod ℓ) pf / ModularCurve.intSeriesC (ZMod ℓ) pg) ∧
      (∀ γ : CongruenceSubgroup.Gamma0 M,
          (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1)) → ρ γ = 1) ∧
      ModularCurve.modularFunctionFieldFullC (ZMod ℓ) M ≤
        ModularCurve.qExpFunctionFieldC (ZMod ℓ) (CohCarrier.GammaH M H) ∧
      (∀ (γ : CongruenceSubgroup.Gamma0 M)
          (x : ModularCurve.qExpFunctionFieldC (ZMod ℓ) (CohCarrier.GammaH M H)),
          (x : LaurentSeries (ZMod ℓ)) ∈ ModularCurve.modularFunctionFieldFullC (ZMod ℓ) M →
            ρ γ x = x) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_zmod.solution
