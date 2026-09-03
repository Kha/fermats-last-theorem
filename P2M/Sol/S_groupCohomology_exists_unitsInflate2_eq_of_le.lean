import Mathlib
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import P2M.Util
namespace P2MW.S_groupCohomology_exists_unitsInflate2_eq_of_le

set_option autoImplicit false

open CategoryTheory groupCohomology

set_option maxHeartbeats 1600000 in
theorem solution
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (L L' : IntermediateField K Ω) [Normal K L] [Normal K L'] (hLL' : L ≤ L')
    (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Additive (L)ˣ) (hf : f ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits K L)) :
    ∃ f' : (L' ≃ₐ[K] L') × (L' ≃ₐ[K] L') → Additive (L')ˣ,
      f' ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits K L') ∧ unitsInflate₂ L' f' = unitsInflate₂ L f := by

  letI : Algebra L L' := (IntermediateField.inclusion hLL').toRingHom.toAlgebra
  haveI : IsScalarTower K L L' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower L L' Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl

  let π' : (L' ≃ₐ[K] L') →* (L ≃ₐ[K] L) := AlgEquiv.restrictNormalHom L
  let ι' : (L)ˣ →* (L')ˣ := Units.map (algebraMap L L').toMonoidHom

  have hππ : ∀ σ : Ω ≃ₐ[K] Ω, π' (AlgEquiv.restrictNormalHom L' σ) = AlgEquiv.restrictNormalHom L σ := by
    intro σ
    apply AlgEquiv.ext
    intro x
    apply (algebraMap L Ω).injective
    show algebraMap L Ω ((AlgEquiv.restrictNormal (AlgEquiv.restrictNormal σ L') L) x)
      = algebraMap L Ω ((AlgEquiv.restrictNormal σ L) x)
    rw [AlgEquiv.restrictNormal_commutes, IsScalarTower.algebraMap_apply L L' Ω,
      AlgEquiv.restrictNormal_commutes, AlgEquiv.restrictNormal_commutes, ← IsScalarTower.algebraMap_apply]
  refine ⟨fun p => Additive.ofMul (ι' (Additive.toMul (f (π' p.1, π' p.2)))), ?_, ?_⟩
  ·
    have hf' := (mem_cocycles₂_iff (A := Rep.ofAlgebraAutOnUnits K L) f).1 hf
    refine (mem_cocycles₂_iff (A := Rep.ofAlgebraAutOnUnits K L') _).2 fun g h j => ?_
    have e := congrArg (fun b : Rep.ofAlgebraAutOnUnits K L =>
      (Additive.ofMul (ι' (Additive.toMul (α := (L)ˣ) b)) : Additive (L')ˣ)) (hf' (π' g) (π' h) (π' j))
    rw [map_mul]
    refine Eq.trans ?_ (Eq.trans e ?_)
    · exact (congrArg Additive.ofMul (map_mul ι' _ _)).trans (ofMul_mul _ _)
    · refine (congrArg Additive.ofMul (map_mul ι' _ _)).trans ((ofMul_mul _ _).trans ?_)
      congr 1

      · apply (Additive.toMul (α := (L')ˣ)).injective
        apply Units.ext
        exact AlgEquiv.restrictNormal_commutes g L _
      · dsimp only
        rw [map_mul]
  · funext ⟨σ, τ⟩
    apply (Additive.toMul (α := Ωˣ)).injective
    apply Units.ext
    show algebraMap L' Ω (algebraMap L L' _) = algebraMap L Ω _
    rw [← IsScalarTower.algebraMap_apply, hππ, hππ]
