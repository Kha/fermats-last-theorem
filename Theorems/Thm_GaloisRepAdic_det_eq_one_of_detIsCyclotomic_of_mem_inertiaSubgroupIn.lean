import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_GaloisRep_LocalConditions
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_det_eq_one_of_detIsCyclotomic_of_mem_inertiaSubgroupIn

set_option autoImplicit false
open IsLocalRing
theorem GaloisRepAdic.det_eq_one_of_detIsCyclotomic_of_mem_inertiaSubgroupIn
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ρ : GaloisRepAdic A) {p : ℕ}
    (hdet : ρ.DetIsCyclotomic p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hp : p.Prime)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ P.inertiaSubgroupIn ℚ) :
    LinearMap.det (ρ.ρ σ) = 1 := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_det_eq_one_of_detIsCyclotomic_of_mem_inertiaSubgroupIn.solution
