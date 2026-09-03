import Mathlib
import Definitions.Def_GaloisRep_LocalConditions
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_exists_mem_inertiaSubgroupIn_residual_ne_one_of_detIsCyclotomic

set_option autoImplicit false
theorem GaloisRepAdic.exists_mem_inertiaSubgroupIn_residual_ne_one_of_detIsCyclotomic
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdet : ρ.DetIsCyclotomic p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p) :
    ∃ τ ∈ P.inertiaSubgroupIn ℚ, ρ.residual.ρ τ ≠ 1 := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_exists_mem_inertiaSubgroupIn_residual_ne_one_of_detIsCyclotomic.solution
