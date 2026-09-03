import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_kummer_decomposition_of_inertia_cocycle
attribute [-instance] groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity
attribute [-simp] groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity

set_option autoImplicit false
theorem ValuationSubring.exists_kummer_decomposition_of_inertia_cocycle
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (N : ℕ)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (p ^ N))
    {M : Type} [AddCommGroup M] [Finite M] (hM : ∀ m : M, (p ^ N) • m = 0)
    (c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M)
    (hlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ s ∈ P.inertiaSubgroupIn ℚ, s ∈ F.fixingSubgroup → c (τ * s) = c τ)
    (hadd : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ τ' ∈ P.inertiaSubgroupIn ℚ,
      (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) →
      (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ' ξ = ξ) → c (τ * τ') = c τ + c τ')
    (hconj : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ a : ℕ, σ ζ = ζ ^ a →
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) →
        c (σ * τ * σ⁻¹) = a • c τ) :
    ∃ (t : ℕ) (x β : Fin t → AlgebraicClosure ℚ) (a : Fin t → M),
      (∀ i, x i ≠ 0) ∧ (∀ i, ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ (x i) = x i) ∧ (∀ i, β i ^ p ^ N = x i) ∧
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) →
        ∀ k : Fin t → ℕ, (∀ i, τ (β i) = ζ ^ (k i) * β i) → c τ = ∑ i, (k i) • a i := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_kummer_decomposition_of_inertia_cocycle.solution
