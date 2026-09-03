import Mathlib
import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_exists_ne_zero_forall_inertiaSubgroupIn_apply_eq_self_of_forall_isRoot_charpoly

set_option autoImplicit false

theorem GaloisRepAdic.exists_ne_zero_forall_inertiaSubgroupIn_apply_eq_self_of_forall_isRoot_charpoly
    {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    (ρ : GaloisRepAdic A) {q : ℕ} (hq : q.Prime) (hqA : IsUnit (q : A))
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (h1 : ∀ σ ∈ P.inertiaSubgroupIn ℚ, (LinearMap.charpoly (ρ.ρ σ)).IsRoot 1) :
    ∃ v : ρ.V, v ≠ 0 ∧ ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ.ρ σ v = v := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_exists_ne_zero_forall_inertiaSubgroupIn_apply_eq_self_of_forall_isRoot_charpoly.solution
