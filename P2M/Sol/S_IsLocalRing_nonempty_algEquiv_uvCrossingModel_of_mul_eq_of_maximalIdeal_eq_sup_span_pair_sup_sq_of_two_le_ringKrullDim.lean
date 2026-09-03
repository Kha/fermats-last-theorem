import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_IsLocalRing_exists_ringEquiv_adicCompletion_uvCrossingModel_of_mul_eq_of_span_pair
import P2M.Util
namespace P2MW.S_IsLocalRing_nonempty_algEquiv_uvCrossingModel_of_mul_eq_of_maximalIdeal_eq_sup_span_pair_sup_sq_of_two_le_ringKrullDim
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open IsLocalRing

theorem solution
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (ϖ : O) (hϖ : Irreducible ϖ)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra O R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (hres : Function.Surjective ((IsLocalRing.residue R).comp (algebraMap O R)))
    (u v : R) (huv : u * v = algebraMap O R ϖ)
    (huv' : IsLocalRing.maximalIdeal R =
      (IsLocalRing.maximalIdeal O).map (algebraMap O R) ⊔ Ideal.span {u, v} ⊔ (IsLocalRing.maximalIdeal R) ^ 2)
    (hdim : 2 ≤ ringKrullDim R) :
    Nonempty (R ≃ₐ[O] ModularCurve.UVCrossingModel O ϖ) := by
  classical

  have hmO : (maximalIdeal O).map (algebraMap O R) ≤ Ideal.span {u, v} := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton, ← huv, Ideal.span_singleton_le_iff_mem]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

  have hm : maximalIdeal R = Ideal.span {u, v} := by
    apply le_antisymm
    · apply Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal R)
        (IsNoetherian.noetherian _) (IsLocalRing.maximalIdeal_le_jacobson _)
      calc maximalIdeal R
          = (maximalIdeal O).map (algebraMap O R) ⊔ Ideal.span {u, v} ⊔ maximalIdeal R ^ 2 := huv'
        _ ≤ Ideal.span {u, v} ⊔ maximalIdeal R • maximalIdeal R := by
          rw [Ideal.smul_eq_mul, ← pow_two]
          exact sup_le (sup_le (hmO.trans le_sup_left) le_sup_left) le_sup_right
    · conv_rhs => rw [huv']
      exact le_sup_of_le_left le_sup_right

  obtain ⟨ι, hιO, -, -⟩ :=
    IsLocalRing.exists_ringEquiv_adicCompletion_uvCrossingModel_of_mul_eq_of_span_pair
      ϖ hϖ u v huv hm hres hdim

  have hbij : Function.Bijective (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
    have h : (algebraMap R (AdicCompletion (maximalIdeal R) R) : R → _) =
        AdicCompletion.of (maximalIdeal R) R := by
      funext r
      rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply]
    rw [h]
    exact AdicCompletion.of_bijective _ _
  let e₁ : R ≃+* AdicCompletion (maximalIdeal R) R := RingEquiv.ofBijective _ hbij
  let e : R ≃+* ModularCurve.UVCrossingModel O ϖ := e₁.trans ι
  refine ⟨AlgEquiv.ofRingEquiv (f := e) ?_⟩
  intro o
  change ι (algebraMap R (AdicCompletion (maximalIdeal R) R) (algebraMap O R o)) = _
  rw [hιO]
  rfl

#print axioms solution
