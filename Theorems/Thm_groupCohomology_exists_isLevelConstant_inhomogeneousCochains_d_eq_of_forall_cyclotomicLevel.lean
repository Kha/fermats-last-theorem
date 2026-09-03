import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_isLevelConstant_inhomogeneousCochains_d_eq_of_forall_cyclotomicLevel
attribute [-instance] WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.coe_continuousH1SrMap_apply groupCohomology.continuousH2SrMap_continuousH2Srπ groupCohomology.coe_levelCocyclesSr₂Map

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.exists_isLevelConstant_inhomogeneousCochains_d_eq_of_forall_cyclotomicLevel
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (hlev : ∀ (K : IntermediateField ℚ (AlgebraicClosure ℚ)), K.IsUnramifiedOutside S → FiniteDimensional ℚ ↥K →
      (∀ s ∈ K.fixingSubgroup, cycloChar p s = 1) →
      ∀ u : (Fin 3 → ↥K.fixingSubgroup) → Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
          ∀ g s : Fin 3 → ↥K.fixingSubgroup,
            (∀ i, ((s i : ↥K.fixingSubgroup) : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ F.fixingSubgroup) → u (g * s) = u g) →
        ((inhomogeneousCochains (Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p))).d 3 4).hom u = 0 →
        ∃ w : (Fin 2 → ↥K.fixingSubgroup) → Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p),
          (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
          ∀ g s : Fin 2 → ↥K.fixingSubgroup,
            (∀ i, ((s i : ↥K.fixingSubgroup) : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ F.fixingSubgroup) → w (g * s) = w g) ∧
          ((inhomogeneousCochains (Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p))).d 2 3).hom w = u)
    (N : Rep.{0} (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) N]
    (hsm : ∀ m : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, N.ρ s m = m)
    (hur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ s ∈ A.inertiaSubgroupIn ℚ, N.ρ s = 1)
    (u : (Fin 3 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) → N)
    (hlc : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ g s : Fin 3 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        (∀ i, s i ∈ F.fixingSubgroup) → u (g * s) = u g)
    (hcoc : ((inhomogeneousCochains N).d 3 4).hom u = 0) :
    ∃ w : (Fin 2 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) → N,
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
        ∀ g s : Fin 2 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
          (∀ i, s i ∈ F.fixingSubgroup) → w (g * s) = w g) ∧
      ((inhomogeneousCochains N).d 2 3).hom w = u := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_isLevelConstant_inhomogeneousCochains_d_eq_of_forall_cyclotomicLevel.solution
