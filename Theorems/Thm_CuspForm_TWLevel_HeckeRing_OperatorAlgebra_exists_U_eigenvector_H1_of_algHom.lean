import Definitions.Def_CuspForm_TWLevelHeckeRing
import P2M.Util
import P2M.Sol.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom
attribute [-instance] IharaLemma.IdempotentSplitting.isScalarTower_base_cornerModule IharaLemma.IdempotentSplitting.isScalarTower_base_cornerRing IharaLemma.IdempotentSplitting.algebraBaseCornerRing IharaLemma.IdempotentSplitting.smulCornerModule IharaLemma.IdempotentSplitting.moduleCornerModule IharaLemma.IdempotentSplitting.isLocalRing_cornerRing IharaLemma.IdempotentSplitting.coeOutCornerRing IharaLemma.IdempotentSplitting.isMaximal_𝔪 IharaLemma.IdempotentSplitting.isScalarTower_cornerModule IharaLemma.IdempotentSplitting.isLocalization_cornerRing
attribute [-simp] IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_apply IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_symm_apply IharaLemma.IdempotentSplitting.coe_cornerSmul IharaLemma.IdempotentSplitting.mk.injEq IharaLemma.IdempotentSplitting.mk.sizeOf_spec IharaLemma.IdempotentSplitting.coe_toCornerRing IharaLemma.toCorner_apply

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open IsLocalRing CuspForm.TWLevel

theorem CuspForm.TWLevel.HeckeRing.OperatorAlgebra.exists_U_eigenvector_H1_of_algHom
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
    (S : Set ℕ) (N : ℕ) [NeZero N] (r : ℕ) [NeZero r]
    (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)
    (t : ℕ) (qv : Fin t → ℕ) [∀ i, NeZero (qv i)] (α : Fin t → ResidueField 𝒪)
    (H : Subgroup (ZMod (level N r qv))ˣ)
    (hc : OpComm N r qv S 𝒪 H) (hdc : DiaComm N r qv S 𝒪 H)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra 𝒪 F]
    (hF : Function.Injective (algebraMap 𝒪 F))
    (lam : HeckeRing N r qv S 𝒪 H θ α hc hdc →ₐ[𝒪] F) :
    ∃ (e : (ZMod (level N r qv))ˣ →* Fˣ) (μ : Fin t → F) (c : CohCarrier.H1 (level N r qv) H F),
      c ≠ 0 ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv),
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT (level N r qv) H ℓ F c) =
          lam (HeckeRing.T N r qv S 𝒪 H θ α hc hdc ℓ hℓ hℓS hℓL) • c) ∧
      (∀ j : Fin t, CohCarrier.heckeT (level N r qv) H (qv j) F c = μ j • c) ∧
      (∀ u : (ZMod (level N r qv))ˣ,
        CohCarrier.diamondL (level N r qv) H F u c = ((e u : Fˣ) : F) • c) ∧
      (∀ (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv),
        ((e u : Fˣ) : F) = lam (HeckeRing.diamond N r qv S 𝒪 H θ α hc hdc u hu)) ∧
      (∀ u : (ZMod (level N r qv))ˣ, u ∈ H → e u = 1) ∧
      (∀ (j : Fin t) (a : 𝒪), IsLocalRing.residue 𝒪 a = α j →
        ∃ P : Polynomial 𝒪, P.Monic ∧ (∀ i < P.natDegree, P.coeff i ∈ maximalIdeal 𝒪) ∧
          Polynomial.aeval (μ j - algebraMap 𝒪 F a) P = 0) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.solution
