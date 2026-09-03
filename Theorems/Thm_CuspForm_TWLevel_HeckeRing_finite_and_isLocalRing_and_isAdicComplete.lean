import Definitions.Def_CuspForm_TWLevelHeckeRing
import P2M.Util
import P2M.Sol.S_CuspForm_TWLevel_HeckeRing_finite_and_isLocalRing_and_isAdicComplete
attribute [-instance] IharaLemma.IdempotentSplitting.isScalarTower_base_cornerModule IharaLemma.IdempotentSplitting.isScalarTower_base_cornerRing IharaLemma.IdempotentSplitting.algebraBaseCornerRing IharaLemma.IdempotentSplitting.smulCornerModule IharaLemma.IdempotentSplitting.moduleCornerModule IharaLemma.IdempotentSplitting.isLocalRing_cornerRing IharaLemma.IdempotentSplitting.coeOutCornerRing IharaLemma.IdempotentSplitting.isMaximal_𝔪 IharaLemma.IdempotentSplitting.isScalarTower_cornerModule IharaLemma.IdempotentSplitting.isLocalization_cornerRing
attribute [-simp] IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_apply IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_symm_apply IharaLemma.IdempotentSplitting.coe_cornerSmul IharaLemma.IdempotentSplitting.mk.injEq IharaLemma.IdempotentSplitting.mk.sizeOf_spec IharaLemma.IdempotentSplitting.coe_toCornerRing IharaLemma.toCorner_apply

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open Polynomial IsLocalRing CuspForm.TWLevel

theorem CuspForm.TWLevel.HeckeRing.finite_and_isLocalRing_and_isAdicComplete
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (S : Set ℕ) (N : ℕ) [NeZero N] (r : ℕ) [NeZero r]
    (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)
    (t : ℕ) (qv : Fin t → ℕ) [∀ i, NeZero (qv i)]
    (πΔ : ∀ i, (ZMod (qv i))ˣ →* Multiplicative (ZMod (p ^ padicValNat p (qv i - 1))))
    (α : Fin t → ResidueField 𝒪)
    (hcQ : OpComm N r qv S 𝒪 (HQ N r qv p πΔ)) (hdc : DiaComm N r qv S 𝒪 (HQ N r qv p πΔ))
    (hM : Nontrivial (ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ)) :
    Module.Finite 𝒪 (HeckeRing N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc) ∧
    IsNoetherianRing (HeckeRing N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc) ∧
    ∃ _ : IsLocalRing (HeckeRing N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc),
      IsAdicComplete (maximalIdeal (HeckeRing N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc))
        (HeckeRing N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc) ∧
      IsLocalHom (algebraMap 𝒪 (HeckeRing N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc)) ∧
      Function.Surjective (residue (HeckeRing N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc) ∘
        algebraMap 𝒪 (HeckeRing N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc)) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_TWLevel_HeckeRing_finite_and_isLocalRing_and_isAdicComplete.solution
