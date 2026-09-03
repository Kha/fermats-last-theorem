import Mathlib
import Definitions.Def_CohCarrier_HeckeData
import P2M.Util
import P2M.Sol.S_CohCarrier_HeckeData_exists_linearEquiv_ML_of_degeneracy_atkinLehner_identities
attribute [-instance] IharaLemma.IdempotentSplitting.isScalarTower_base_cornerModule IharaLemma.IdempotentSplitting.isScalarTower_base_cornerRing IharaLemma.IdempotentSplitting.algebraBaseCornerRing IharaLemma.IdempotentSplitting.smulCornerModule IharaLemma.IdempotentSplitting.moduleCornerModule IharaLemma.IdempotentSplitting.isLocalRing_cornerRing IharaLemma.IdempotentSplitting.coeOutCornerRing IharaLemma.IdempotentSplitting.isMaximal_𝔪 IharaLemma.IdempotentSplitting.isScalarTower_cornerModule IharaLemma.IdempotentSplitting.isLocalization_cornerRing
attribute [-simp] IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_apply IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_symm_apply IharaLemma.IdempotentSplitting.coe_cornerSmul IharaLemma.IdempotentSplitting.mk.injEq IharaLemma.IdempotentSplitting.mk.sizeOf_spec IharaLemma.IdempotentSplitting.coe_toCornerRing IharaLemma.toCorner_apply

set_option autoImplicit false
attribute [local instance] CohCarrier.HeckeData.moduleFreeAlg

open CohCarrier

theorem CohCarrier.HeckeData.exists_linearEquiv_ML_of_degeneracy_atkinLehner_identities
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))

    {V W : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V] [AddCommGroup W] [Module 𝒪 W]
    (DV : HeckeData 𝒪 V k) (DW : HeckeData 𝒪 W k)

    {G : Type} (σV : G ⊕ Unit ≃ DV.Gen) (σW : G ⊕ Unit ≃ DW.Gen)
    (hθ : ∀ g : G, DW.θbar (σW (Sum.inl g)) = DV.θbar (σV (Sum.inl g)))

    (ι : V →ₗ[𝒪] W) (j : W →ₗ[𝒪] V) (w : Module.End 𝒪 W)
    (hι : ∀ g : G, ι ∘ₗ DV.op (σV (Sum.inl g)) = DW.op (σW (Sum.inl g)) ∘ₗ ι)
    (hj : ∀ g : G, j ∘ₗ DW.op (σW (Sum.inl g)) = DV.op (σV (Sum.inl g)) ∘ₗ j)
    (hw : ∀ g : G, w * DW.op (σW (Sum.inl g)) = DW.op (σW (Sum.inl g)) * w)

    (q : ℕ) (d : G) (hdV : IsUnit (DV.op (σV (Sum.inl d)))) (hdW : IsUnit (DW.op (σW (Sum.inl d))))

    (h₁ : w ∘ₗ ι = (ι ∘ₗ DV.op (σV (Sum.inr ())) - DW.op (σW (Sum.inr ())) ∘ₗ ι) ∘ₗ
      DV.op (σV (Sum.inl d)))
    (h₂ : j ∘ₗ ι = ((q : 𝒪) + 1) • LinearMap.id)
    (h₃ : j ∘ₗ w ∘ₗ ι = DV.op (σV (Sum.inr ())) * DV.op (σV (Sum.inl d)))
    (h₄ : ι ∘ₗ j = LinearMap.id + DW.op (σW (Sum.inr ())) * w)
    (h₅ : w * w = DW.op (σW (Sum.inl d)))

    (hq : (q : k) = 1) (hd : DV.θbar (σV (Sum.inl d)) = 1)
    (α β : k) (hα : DW.θbar (σW (Sum.inr ())) = α) (hT : DV.θbar (σV (Sum.inr ())) = α + β)
    (hαβ : α * β = 1) (hne : α ≠ β) :
    ∃ e : DW.ML ≃ₗ[𝒪] DV.ML, ∀ (g : G) (x : DW.ML),
      e ((MvPolynomial.X (σW (Sum.inl g)) : DW.FreeAlg) • x) =
        (MvPolynomial.X (σV (Sum.inl g)) : DV.FreeAlg) • e x := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_HeckeData_exists_linearEquiv_ML_of_degeneracy_atkinLehner_identities.solution
