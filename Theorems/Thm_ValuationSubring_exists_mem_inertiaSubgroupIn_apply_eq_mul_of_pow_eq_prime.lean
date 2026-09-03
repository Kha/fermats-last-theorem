import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_mul_of_pow_eq_prime
attribute [-instance] AlgebraicClosure.Rat.isGalois groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity
attribute [-simp] groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity

set_option autoImplicit false

theorem ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_mul_of_pow_eq_prime
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (N : ℕ) (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (p ^ N)) {t : ℕ} (u β : Fin t → AlgebraicClosure ℚ)
    (hu : ∀ i, P.valuation (u i) = 1) (huI : ∀ i, ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ (u i) = u i)
    (hβ : ∀ i, β i ^ p ^ N = u i) (ϖ : AlgebraicClosure ℚ) (hϖ : ϖ ^ p ^ N = (p : AlgebraicClosure ℚ)) :
    ∃ τ ∈ P.inertiaSubgroupIn ℚ,
      (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) ∧ (∀ i, τ (β i) = β i) ∧ τ ϖ = ζ * ϖ := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_mul_of_pow_eq_prime.solution
