import Mathlib
import Definitions.Def_GaloisRep_LocalConditions
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_exists_mem_inertiaSubgroupIn_apply_ne_one_of_detIsCyclotomic

theorem GaloisRepAdic.exists_mem_inertiaSubgroupIn_apply_ne_one_of_detIsCyclotomic
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) {p : ℕ} (hp : p.Prime)
    (hp0 : (p : A) ≠ 0) (hdet : ρ.DetIsCyclotomic p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p) :
    ∃ σ ∈ P.inertiaSubgroupIn ℚ, ρ.ρ σ ≠ 1 := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_exists_mem_inertiaSubgroupIn_apply_ne_one_of_detIsCyclotomic.solution
