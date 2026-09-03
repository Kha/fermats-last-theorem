import Mathlib
import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_rho_mul_comm_of_mem_inertiaSubgroupIn_of_forall_isRoot_charpoly

set_option autoImplicit false

theorem GaloisRepAdic.rho_mul_comm_of_mem_inertiaSubgroupIn_of_forall_isRoot_charpoly
    {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    (ρ : GaloisRepAdic A) {q : ℕ} (hq : q.Prime) (hqA : IsUnit (q : A))
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (h1 : ∀ σ ∈ P.inertiaSubgroupIn ℚ, (LinearMap.charpoly (ρ.ρ σ)).IsRoot 1)
    {σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (hτ : τ ∈ P.inertiaSubgroupIn ℚ) :
    ρ.ρ σ * ρ.ρ τ = ρ.ρ τ * ρ.ρ σ := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_rho_mul_comm_of_mem_inertiaSubgroupIn_of_forall_isRoot_charpoly.solution
