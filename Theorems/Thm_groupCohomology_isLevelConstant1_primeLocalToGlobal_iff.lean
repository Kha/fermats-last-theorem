import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import P2M.Util
import P2M.Sol.S_groupCohomology_isLevelConstant1_primeLocalToGlobal_iff

set_option autoImplicit false
open ExtCitation groupCohomology
theorem groupCohomology.isLevelConstant1_primeLocalToGlobal_iff
    (q : Nat.Primes) [Fact (q : ℕ).Prime] {X : Type*}
    (f : primeLocalGaloisGroup q → X) :
    IsLevelConstant₁ (primeLocalToGlobal q) f ↔
      ∃ K : IntermediateField ℚ_[(q : ℕ)] (PadicAlgCl (q : ℕ)), FiniteDimensional ℚ_[(q : ℕ)] K ∧
        ∀ g s : primeLocalGaloisGroup q, s ∈ K.fixingSubgroup → f (g * s) = f g := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_isLevelConstant1_primeLocalToGlobal_iff.solution
