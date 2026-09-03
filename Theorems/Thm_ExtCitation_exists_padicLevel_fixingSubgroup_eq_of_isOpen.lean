import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import P2M.Util
import P2M.Sol.S_ExtCitation_exists_padicLevel_fixingSubgroup_eq_of_isOpen

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open ExtCitation
theorem ExtCitation.exists_padicLevel_fixingSubgroup_eq_of_isOpen (q : Nat.Primes) [Fact (q : ℕ).Prime]
    (S : Subgroup (primeLocalGaloisGroup q))
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S) :
    ∃ K : IntermediateField ℚ_[(q : ℕ)] (PadicAlgCl (q : ℕ)), FiniteDimensional ℚ_[(q : ℕ)] K ∧
      (K.fixingSubgroup : Subgroup (primeLocalGaloisGroup q)) = S := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_exists_padicLevel_fixingSubgroup_eq_of_isOpen.solution
