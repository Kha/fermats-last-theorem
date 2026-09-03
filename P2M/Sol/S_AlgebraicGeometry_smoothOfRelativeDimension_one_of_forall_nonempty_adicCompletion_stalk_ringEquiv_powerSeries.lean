import Mathlib
import Theorems.Thm_IsLocalRing_isDiscreteValuationRing_of_nonempty_adicCompletion_ringEquiv_powerSeries
import Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_of_forall_isClosed_isRegularLocalRing_stalk
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_smoothOfRelativeDimension_one_of_forall_nonempty_adicCompletion_stalk_ringEquiv_powerSeries
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (h : ∀ y : ↥Y, IsClosed ({y} : Set ↥Y) →
      Nonempty (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y) ≃+* PowerSeries k)) :
    SmoothOfRelativeDimension 1 g := by
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  apply AlgebraicGeometry.smoothOfRelativeDimension_of_forall_isClosed_isRegularLocalRing_stalk k g 1
  intro y hy
  obtain ⟨hdom, hdvr⟩ := IsLocalRing.isDiscreteValuationRing_of_nonempty_adicCompletion_ringEquiv_powerSeries
    (Y.presheaf.stalk y) k (h y hy)
  haveI := hdom; haveI := hdvr
  refine ⟨inferInstance, ?_⟩
  rw [IsDiscreteValuationRing.ringKrullDim_eq_one]
  rfl
