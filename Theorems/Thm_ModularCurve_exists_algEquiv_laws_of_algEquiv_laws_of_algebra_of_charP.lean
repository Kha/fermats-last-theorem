import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_algEquiv_laws_of_algEquiv_laws_of_algebra_of_charP
attribute [-simp] CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply

set_option autoImplicit false

theorem ModularCurve.exists_algEquiv_laws_of_algEquiv_laws_of_algebra_of_charP
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hcop : ℓ.Coprime N) (hNK : ((N : ℕ) : K) ≠ 0) (hℓK : ((ℓ : ℕ) : K) ≠ 0)
    (κ : Type*) [Field κ] [Algebra κ K]
    (hβκ : ModularCurve.HeckeBetaModLHDefined κ N H' ℓ) (hβK : ModularCurve.HeckeBetaModLHDefined K N H' ℓ)
    (ρκ : CongruenceSubgroup.Gamma0 N →* (↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')) ≃ₐ[κ] ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H'))))
    (hρκ : ModularCurve.IsDiamondPullbackModL κ N H' ρκ)
    (ρK : CongruenceSubgroup.Gamma0 N →* (↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) ≃ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))))
    (hρK : ModularCurve.IsDiamondPullbackModL K N H' ρK)
    (Wκ : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) ≃ₐ[κ] ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))))
    (hWκ :
      (∀ x : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')),
        (x : LaurentSeries κ) ∈ ModularCurve.modularFunctionFieldC κ N →
          Wκ (ModularCurve.heckeAlphaModLH κ N H' ℓ x) = ModularCurve.heckeBetaModLH κ N H' ℓ x) ∧
      (∀ x : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')),
        (x : LaurentSeries κ) ∈ ModularCurve.modularFunctionFieldC κ N →
          Wκ (ModularCurve.heckeBetaModLH κ N H' ℓ x) = ModularCurve.heckeAlphaModLH κ N H' ℓ x) ∧
      (∀ x : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')),
        Wκ (ModularCurve.heckeAlphaModLH κ N H' ℓ x) =
          ModularCurve.heckeBetaModLH κ N H' ℓ (ρκ (CuspForm.gammaLift N (ZMod.unitOfCoprime ℓ hcop)⁻¹) x)) ∧
      (∀ x : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH N H')),
        Wκ (ModularCurve.heckeBetaModLH κ N H' ℓ x) = ModularCurve.heckeAlphaModLH κ N H' ℓ x)) :
    ∃ WK : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) ≃ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))),
      (∀ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')),
        (x : LaurentSeries K) ∈ ModularCurve.modularFunctionFieldC K N →
          WK (ModularCurve.heckeAlphaModLH K N H' ℓ x) = ModularCurve.heckeBetaModLH K N H' ℓ x) ∧
      (∀ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')),
        (x : LaurentSeries K) ∈ ModularCurve.modularFunctionFieldC K N →
          WK (ModularCurve.heckeBetaModLH K N H' ℓ x) = ModularCurve.heckeAlphaModLH K N H' ℓ x) ∧
      (∀ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')),
        WK (ModularCurve.heckeAlphaModLH K N H' ℓ x) =
          ModularCurve.heckeBetaModLH K N H' ℓ (ρK (CuspForm.gammaLift N (ZMod.unitOfCoprime ℓ hcop)⁻¹) x)) ∧
      (∀ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')),
        WK (ModularCurve.heckeBetaModLH K N H' ℓ x) = ModularCurve.heckeAlphaModLH K N H' ℓ x) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_algEquiv_laws_of_algEquiv_laws_of_algebra_of_charP.solution
