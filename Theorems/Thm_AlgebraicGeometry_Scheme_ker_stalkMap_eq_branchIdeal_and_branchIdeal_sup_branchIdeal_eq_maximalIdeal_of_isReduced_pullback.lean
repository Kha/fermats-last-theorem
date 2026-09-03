import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageCrossingFrame
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_ker_stalkMap_eq_branchIdeal_and_branchIdeal_sup_branchIdeal_eq_maximalIdeal_of_isReduced_pullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.ker_stalkMap_eq_branchIdeal_and_branchIdeal_sup_branchIdeal_eq_maximalIdeal_of_isReduced_pullback
    {k : Type u} [Field k] {Y C₁ C₂ : Scheme.{u}}
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsIntegral C₁] [SmoothOfRelativeDimension 1 c₁] [IsIntegral C₂] [SmoothOfRelativeDimension 1 c₂]
    (i₁ : C₁ ⟶ Y) (i₂ : C₂ ⟶ Y) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hcover : ∀ z : ↥Y, z ∈ Set.range i₁.base ∨ z ∈ Set.range i₂.base)
    [IsReduced (pullback i₁ i₂)] [Finite ↥(pullback i₁ i₂)] (ν : ↥(pullback i₁ i₂))
    (hk₁ : i₁.base (genericPoint C₁) ⤳ i₁.base ((pullback.fst i₁ i₂).base ν))
    (hy₂ : i₂.base ((pullback.snd i₁ i₂).base ν) = i₁.base ((pullback.fst i₁ i₂).base ν))
    (hk₂ : i₂.base (genericPoint C₂) ⤳ i₁.base ((pullback.fst i₁ i₂).base ν)) :
    RingHom.ker (i₁.stalkMap ((pullback.fst i₁ i₂).base ν)).hom = Scheme.branchIdeal hk₁ ∧
    (RingHom.ker (i₂.stalkMap ((pullback.snd i₁ i₂).base ν)).hom).comap
        (Y.presheaf.stalkSpecializes (specializes_of_eq hy₂)).hom = Scheme.branchIdeal hk₂ ∧
    Scheme.branchIdeal hk₁ ⊔ Scheme.branchIdeal hk₂ =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk (i₁.base ((pullback.fst i₁ i₂).base ν))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_ker_stalkMap_eq_branchIdeal_and_branchIdeal_sup_branchIdeal_eq_maximalIdeal_of_isReduced_pullback.solution
