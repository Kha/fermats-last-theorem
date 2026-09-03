import Definitions.Def_CohCarrier_Inst
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CohCarrier_HeckeData_exists_eigenvector_H1_of_toML_ne_zero
attribute [-instance] IharaLemma.IdempotentSplitting.isScalarTower_base_cornerModule IharaLemma.IdempotentSplitting.isScalarTower_base_cornerRing IharaLemma.IdempotentSplitting.algebraBaseCornerRing IharaLemma.IdempotentSplitting.smulCornerModule IharaLemma.IdempotentSplitting.moduleCornerModule IharaLemma.IdempotentSplitting.isLocalRing_cornerRing IharaLemma.IdempotentSplitting.coeOutCornerRing IharaLemma.IdempotentSplitting.isMaximal_𝔪 IharaLemma.IdempotentSplitting.isScalarTower_cornerModule IharaLemma.IdempotentSplitting.isLocalization_cornerRing
attribute [-simp] IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_apply IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_symm_apply IharaLemma.IdempotentSplitting.coe_cornerSmul IharaLemma.IdempotentSplitting.mk.injEq IharaLemma.IdempotentSplitting.mk.sizeOf_spec IharaLemma.IdempotentSplitting.coe_toCornerRing IharaLemma.toCorner_apply

set_option autoImplicit false

open IsLocalRing

theorem CohCarrier.HeckeData.exists_eigenvector_H1_of_toML_ne_zero
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : CohCarrier.HeckeData 𝒪 (CohCarrier.H1 M H 𝒪) (ResidueField 𝒪))

    (ℓ : D.Gen → ℕ) (hℓ : ∀ g : D.Gen, (ℓ g).Prime)
    (hop : ∀ (g : D.Gen) (ψ : CohCarrier.H1 M H 𝒪),
      D.op g ψ = (haveI : NeZero (ℓ g) := ⟨(hℓ g).ne_zero⟩; CohCarrier.heckeT M H (ℓ g) 𝒪 ψ))

    (W : Submodule 𝒪 (CohCarrier.H1 M H 𝒪)) (hW : ∀ (g : D.Gen), ∀ w ∈ W, D.op g w ∈ W)
    (φ : CohCarrier.H1 M H 𝒪) (hφW : φ ∈ W) (hφ : D.toML φ ≠ 0) :
    ∃ (𝒪' : Type) (_ : CommRing 𝒪') (_ : IsDomain 𝒪') (_ : IsDiscreteValuationRing 𝒪')
      (_ : IsAdicComplete (maximalIdeal 𝒪') 𝒪') (_ : Finite (ResidueField 𝒪'))
      (_ : CharZero 𝒪') (_ : Algebra 𝒪 𝒪') (_ : Module.Finite 𝒪 𝒪')
      (_ : IsLocalHom (algebraMap 𝒪 𝒪')),
    Function.Injective (algebraMap 𝒪 𝒪') ∧
    ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (_ : Algebra 𝒪' F),
    Function.Injective (algebraMap 𝒪' F) ∧
    ∃ lam : D.Gen → 𝒪',
      (∀ g : D.Gen, residue 𝒪' (lam g) = ResidueField.map (algebraMap 𝒪 𝒪') (D.θbar g)) ∧
      ∃ c : CohCarrier.H1 M H F, c ≠ 0 ∧
        c ∈ Submodule.span F
          ((fun w : CohCarrier.H1 M H 𝒪 =>
              ((algebraMap 𝒪' F).comp (algebraMap 𝒪 𝒪')).toAddMonoidHom.comp w) '' (W : Set _)) ∧
        ∀ g : D.Gen,
          (haveI : NeZero (ℓ g) := ⟨(hℓ g).ne_zero⟩; CohCarrier.heckeT M H (ℓ g) F c) =
            algebraMap 𝒪' F (lam g) • c := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_HeckeData_exists_eigenvector_H1_of_toML_ne_zero.solution
