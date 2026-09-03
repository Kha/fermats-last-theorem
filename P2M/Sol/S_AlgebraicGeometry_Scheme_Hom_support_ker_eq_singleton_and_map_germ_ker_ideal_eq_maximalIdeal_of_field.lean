import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_map_germ_ker_ideal_eq_ker_stalkMap
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_support_ker_eq_singleton_and_map_germ_ker_ideal_eq_maximalIdeal_of_field

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

theorem solution
    {K : Type u} [Field K] {C : Scheme.{u}} (σ : Spec (CommRingCat.of K) ⟶ C) [IsClosedImmersion σ] :
    ((σ.ker).support : Set ↥C) = {σ.base (IsLocalRing.closedPoint K)} ∧
    ∀ (U : C.affineOpens) (hx : σ.base (IsLocalRing.closedPoint K) ∈ (U : C.Opens)),
      Ideal.map (C.presheaf.germ (U : C.Opens) (σ.base (IsLocalRing.closedPoint K)) hx).hom (σ.ker.ideal U) =
        IsLocalRing.maximalIdeal (C.presheaf.stalk (σ.base (IsLocalRing.closedPoint K))) := by  classical
  have hrange : Set.range σ.base = {σ.base (IsLocalRing.closedPoint K)} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact congrArg σ.base (Subsingleton.elim y _)
    · rintro rfl
      exact ⟨_, rfl⟩
  refine ⟨?_, fun U hx => ?_⟩
  ·
    rw [Scheme.Hom.support_ker]
    show closure (Set.range σ.base) = _
    rw [σ.isClosedEmbedding.isClosed_range.closure_eq, hrange]
  · rw [Scheme.Hom.map_germ_ker_ideal_eq_ker_stalkMap σ (IsLocalRing.closedPoint K) U hx]

    have hbot : IsLocalRing.maximalIdeal ((Spec (CommRingCat.of K)).presheaf.stalk (IsLocalRing.closedPoint K)) = ⊥ := by
      rw [← IsLocalRing.isField_iff_maximalIdeal_eq]
      exact MulEquiv.isField (Field.toIsField K)
        (stalkClosedPointIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv
    apply le_antisymm
    · intro a ha
      rw [RingHom.mem_ker] at ha
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have := hu.map (σ.stalkMap (IsLocalRing.closedPoint K)).hom
      rw [ha] at this
      exact not_isUnit_zero this
    · intro a ha
      rw [RingHom.mem_ker, ← Ideal.mem_bot, ← hbot, IsLocalRing.mem_maximalIdeal]
      exact map_nonunit (σ.stalkMap (IsLocalRing.closedPoint K)).hom a ((IsLocalRing.mem_maximalIdeal _).mp ha)
