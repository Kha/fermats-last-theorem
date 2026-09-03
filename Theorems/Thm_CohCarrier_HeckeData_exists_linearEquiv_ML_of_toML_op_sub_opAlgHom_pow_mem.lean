import Mathlib
import Definitions.Def_CohCarrier_HeckeData
import P2M.Util
import P2M.Sol.S_CohCarrier_HeckeData_exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem
attribute [-instance] IharaLemma.IdempotentSplitting.isScalarTower_base_cornerModule IharaLemma.IdempotentSplitting.isScalarTower_base_cornerRing IharaLemma.IdempotentSplitting.algebraBaseCornerRing IharaLemma.IdempotentSplitting.smulCornerModule IharaLemma.IdempotentSplitting.moduleCornerModule IharaLemma.IdempotentSplitting.isLocalRing_cornerRing IharaLemma.IdempotentSplitting.coeOutCornerRing IharaLemma.IdempotentSplitting.isMaximal_𝔪 IharaLemma.IdempotentSplitting.isScalarTower_cornerModule IharaLemma.IdempotentSplitting.isLocalization_cornerRing
attribute [-simp] IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_apply IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_symm_apply IharaLemma.IdempotentSplitting.coe_cornerSmul IharaLemma.IdempotentSplitting.mk.injEq IharaLemma.IdempotentSplitting.mk.sizeOf_spec IharaLemma.IdempotentSplitting.coe_toCornerRing IharaLemma.toCorner_apply

set_option autoImplicit false
attribute [local instance] CohCarrier.HeckeData.moduleFreeAlg

open CohCarrier

theorem CohCarrier.HeckeData.exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]

    (DV DE : HeckeData 𝒪 V k) (σ : DV.Gen ⊕ Unit ≃ DE.Gen)
    (hop : ∀ g : DV.Gen, DE.op (σ (Sum.inl g)) = DV.op g)
    (hθ : ∀ g : DV.Gen, DE.θbar (σ (Sum.inl g)) = DV.θbar g)

    (z₀ : DV.FreeAlg) (hz : DE.θbar (σ (Sum.inr ())) = DV.thetaTilde z₀)

    (n : ℕ) (hnil : ∀ v : V, DV.toML (((DE.op (σ (Sum.inr ())) - DV.opAlgHom z₀) ^ n) v) ∈
      (IsLocalRing.maximalIdeal 𝒪) • (⊤ : Submodule 𝒪 DV.ML)) :
    ∃ e : DE.ML ≃ₗ[𝒪] DV.ML, ∀ (g : DV.Gen) (x : DE.ML),
      e ((MvPolynomial.X (σ (Sum.inl g)) : DE.FreeAlg) • x) = (MvPolynomial.X g : DV.FreeAlg) • e x := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_HeckeData_exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem.solution
