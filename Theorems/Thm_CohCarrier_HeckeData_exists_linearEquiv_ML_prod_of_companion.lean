import Mathlib
import Definitions.Def_CohCarrier_HeckeData
import P2M.Util
import P2M.Sol.S_CohCarrier_HeckeData_exists_linearEquiv_ML_prod_of_companion
attribute [-instance] IharaLemma.IdempotentSplitting.isScalarTower_base_cornerModule IharaLemma.IdempotentSplitting.isScalarTower_base_cornerRing IharaLemma.IdempotentSplitting.algebraBaseCornerRing IharaLemma.IdempotentSplitting.smulCornerModule IharaLemma.IdempotentSplitting.moduleCornerModule IharaLemma.IdempotentSplitting.isLocalRing_cornerRing IharaLemma.IdempotentSplitting.coeOutCornerRing IharaLemma.IdempotentSplitting.isMaximal_𝔪 IharaLemma.IdempotentSplitting.isScalarTower_cornerModule IharaLemma.IdempotentSplitting.isLocalization_cornerRing
attribute [-simp] IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_apply IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_symm_apply IharaLemma.IdempotentSplitting.coe_cornerSmul IharaLemma.IdempotentSplitting.mk.injEq IharaLemma.IdempotentSplitting.mk.sizeOf_spec IharaLemma.IdempotentSplitting.coe_toCornerRing IharaLemma.toCorner_apply

set_option autoImplicit false
attribute [local instance] CohCarrier.HeckeData.moduleFreeAlg

open CohCarrier

theorem CohCarrier.HeckeData.exists_linearEquiv_ML_prod_of_companion
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]

    (DV : HeckeData 𝒪 V k) (DP : HeckeData 𝒪 (V × V) k)

    {G : Type} (σV : G ⊕ Unit ≃ DV.Gen) (σP : G ⊕ Unit ≃ DP.Gen)
    (hθ : ∀ g : G, DP.θbar (σP (Sum.inl g)) = DV.θbar (σV (Sum.inl g)))

    (c : 𝒪) (d : G) (Dinv : Module.End 𝒪 V)
    (hDinv : DV.op (σV (Sum.inl d)) * Dinv = 1) (hDinv' : Dinv * DV.op (σV (Sum.inl d)) = 1)

    (hop_inl : ∀ g : G,
      DP.op (σP (Sum.inl g)) = (DV.op (σV (Sum.inl g))).prodMap (DV.op (σV (Sum.inl g))))
    (hop_inr : DP.op (σP (Sum.inr ())) =
      (DV.op (σV (Sum.inr ())) ∘ₗ LinearMap.fst 𝒪 V V + c • LinearMap.snd 𝒪 V V).prod
        (-(Dinv ∘ₗ LinearMap.fst 𝒪 V V)))

    (α β : k) (hα : DP.θbar (σP (Sum.inr ())) = α) (hT : DV.θbar (σV (Sum.inr ())) = α + β)
    (hprod : α * β * DV.θbar (σV (Sum.inl d)) = algebraMap 𝒪 k c) (hc : algebraMap 𝒪 k c ≠ 0)
    (hne : α ≠ β) :
    ∃ e : DP.ML ≃ₗ[𝒪] DV.ML, ∀ (g : G) (x : DP.ML),
      e ((MvPolynomial.X (σP (Sum.inl g)) : DP.FreeAlg) • x) =
        (MvPolynomial.X (σV (Sum.inl g)) : DV.FreeAlg) • e x := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_HeckeData_exists_linearEquiv_ML_prod_of_companion.solution
