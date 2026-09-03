import Definitions.Def_ExtEndgame_ProductionDatum
import P2M.Util
import P2M.Sol.S_ExtCitation_forall_exists_finiteDimensional_primeLocalToGlobal_iff

set_option autoImplicit false
open CategoryTheory ExtCitation
theorem ExtCitation.forall_exists_finiteDimensional_primeLocalToGlobal_iff
    (q : Nat.Primes) [Fact (q : ℕ).Prime]
    {k : Type} [CommRing k] (M : Rep k (primeLocalGaloisGroup q)) :
    (∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ s, primeLocalToGlobal q s ∈ F.fixingSubgroup → M.ρ s m = m) ↔
      ∀ m : M, ∃ K : IntermediateField ℚ_[(q : ℕ)] (PadicAlgCl (q : ℕ)), FiniteDimensional ℚ_[(q : ℕ)] K ∧
        ∀ s : primeLocalGaloisGroup q, s ∈ K.fixingSubgroup → M.ρ s m = m := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_forall_exists_finiteDimensional_primeLocalToGlobal_iff.solution
