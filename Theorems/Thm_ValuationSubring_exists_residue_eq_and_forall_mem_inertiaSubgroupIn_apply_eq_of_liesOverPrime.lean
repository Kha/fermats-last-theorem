import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_residue_eq_and_forall_mem_inertiaSubgroupIn_apply_eq_of_liesOverPrime

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.exists_residue_eq_and_forall_mem_inertiaSubgroupIn_apply_eq_of_liesOverPrime
    (A : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ} (hp : p.Prime) (hA : A.LiesOverPrime p)
    (x : IsLocalRing.ResidueField ↥A) :
    ∃ a : ↥A, IsLocalRing.residue ↥A a = x ∧
      ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ (a : AlgebraicClosure ℚ) = a := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_residue_eq_and_forall_mem_inertiaSubgroupIn_apply_eq_of_liesOverPrime.solution
