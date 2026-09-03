import Definitions.Def_CuspForm_TWLevelHeckeModule
import Mathlib.RingTheory.AdicCompletion.Basic
import P2M.Util
import P2M.Sol.S_CuspForm_TWLevel_exists_linearEquiv_ML_HR_init_of_toML_diamondL_eq
attribute [-instance] CuspForm.TWLevel.HeckeRing.instAlgebra CuspForm.TWLevel.heckeSubalgebra_isMulCommutative CuspForm.TWLevel.HeckeRing.instInhabited CuspForm.TWLevel.HeckeRing.instCommRing CohCarrier.GammaHLower_finiteIndex IharaLemma.IdempotentSplitting.isScalarTower_base_cornerModule IharaLemma.IdempotentSplitting.isScalarTower_base_cornerRing IharaLemma.IdempotentSplitting.algebraBaseCornerRing IharaLemma.IdempotentSplitting.smulCornerModule IharaLemma.IdempotentSplitting.moduleCornerModule IharaLemma.IdempotentSplitting.isLocalRing_cornerRing IharaLemma.IdempotentSplitting.coeOutCornerRing IharaLemma.IdempotentSplitting.isMaximal_𝔪 IharaLemma.IdempotentSplitting.isScalarTower_cornerModule IharaLemma.IdempotentSplitting.isLocalization_cornerRing
attribute [-simp] CuspForm.TWLevel.opML_apply CuspForm.TWLevel.HeckeRing.act_diamond CuspForm.TWLevel.HeckeRing.act_T CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_apply IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_symm_apply IharaLemma.IdempotentSplitting.coe_cornerSmul IharaLemma.IdempotentSplitting.mk.injEq IharaLemma.IdempotentSplitting.mk.sizeOf_spec IharaLemma.IdempotentSplitting.coe_toCornerRing IharaLemma.toCorner_apply

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open IsLocalRing CuspForm.TWLevel

theorem CuspForm.TWLevel.exists_linearEquiv_ML_HR_init_of_toML_diamondL_eq
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪]

    (S : Set ℕ) (N : ℕ) [NeZero N] (r : ℕ) [NeZero r]

    (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)

    {t : ℕ} (qv : Fin (t + 1) → ℕ) (hq : ∀ i, (qv i).Prime) (hqS : qv (Fin.last t) ∉ S)
    (hqL : ¬ qv (Fin.last t) ∣ level N r (Fin.init qv))
    (hq1 : ((qv (Fin.last t) : ℕ) : ResidueField 𝒪) = 1)

    (α : Fin (t + 1) → ResidueField 𝒪)
    (hα : α (Fin.last t) ^ 2 -
          θ (CuspForm.heckeAlgebra.T (hq (Fin.last t))
            (not_dvd_of_not_dvd_level N r (Fin.init qv) hqL) hqS) * α (Fin.last t) +
            (qv (Fin.last t) : ResidueField 𝒪) = 0 ∧
      2 * α (Fin.last t) ≠
        θ (CuspForm.heckeAlgebra.T (hq (Fin.last t))
          (not_dvd_of_not_dvd_level N r (Fin.init qv) hqL) hqS))

    (hc₁ : haveI : ∀ i, NeZero (qv i) := fun i => ⟨(hq i).ne_zero⟩
      OpComm N r qv S 𝒪 (HR N r qv))
    (hc₀ : haveI : ∀ i, NeZero (Fin.init qv i) := fun i => ⟨(hq i.castSucc).ne_zero⟩
      OpComm N r (Fin.init qv) S 𝒪 (HR N r (Fin.init qv))) :
    haveI : ∀ i, NeZero (qv i) := fun i => ⟨(hq i).ne_zero⟩
    haveI : ∀ i, NeZero (Fin.init qv i) := fun i => ⟨(hq i.castSucc).ne_zero⟩

    (∀ (u : (ZMod (level N r qv))ˣ) (v : Carrier N r qv 𝒪 (HR N r qv)),
      (heckeData N r qv S 𝒪 (HR N r qv) θ α hc₁).toML
          (CohCarrier.diamondL (level N r qv) (HR N r qv) 𝒪 u v) =
        (heckeData N r qv S 𝒪 (HR N r qv) θ α hc₁).toML v) →
    (∀ (u : (ZMod (level N r (Fin.init qv)))ˣ) (v : Carrier N r (Fin.init qv) 𝒪 (HR N r (Fin.init qv))),
      (heckeData N r (Fin.init qv) S 𝒪 (HR N r (Fin.init qv)) θ (Fin.init α) hc₀).toML
          (CohCarrier.diamondL (level N r (Fin.init qv)) (HR N r (Fin.init qv)) 𝒪 u v) =
        (heckeData N r (Fin.init qv) S 𝒪 (HR N r (Fin.init qv)) θ (Fin.init α) hc₀).toML v) →
    ∃ e : ML N r qv S 𝒪 (HR N r qv) θ α hc₁ ≃ₗ[𝒪]
        ML N r (Fin.init qv) S 𝒪 (HR N r (Fin.init qv)) θ (Fin.init α) hc₀,

      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv)
          (hℓL' : ¬ ℓ ∣ level N r (Fin.init qv)) (x : ML N r qv S 𝒪 (HR N r qv) θ α hc₁),
        e ((MvPolynomial.X (Gen.T ℓ hℓ hℓS hℓL) :
            (heckeData N r qv S 𝒪 (HR N r qv) θ α hc₁).FreeAlg) • x) =
          (MvPolynomial.X (Gen.T ℓ hℓ hℓS hℓL') :
            (heckeData N r (Fin.init qv) S 𝒪 (HR N r (Fin.init qv)) θ (Fin.init α) hc₀).FreeAlg) •
            e x) ∧

      (∀ (i : Fin t) (x : ML N r qv S 𝒪 (HR N r qv) θ α hc₁),
        e ((MvPolynomial.X (Gen.U i.castSucc) :
            (heckeData N r qv S 𝒪 (HR N r qv) θ α hc₁).FreeAlg) • x) =
          (MvPolynomial.X (Gen.U i) :
            (heckeData N r (Fin.init qv) S 𝒪 (HR N r (Fin.init qv)) θ (Fin.init α) hc₀).FreeAlg) •
            e x) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_TWLevel_exists_linearEquiv_ML_HR_init_of_toML_diamondL_eq.solution
