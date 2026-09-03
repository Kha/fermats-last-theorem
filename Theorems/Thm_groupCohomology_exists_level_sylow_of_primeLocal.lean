import Definitions.Def_ExtEndgame_ProductionDatum
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_level_sylow_of_primeLocal
attribute [-instance] ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation
theorem groupCohomology.exists_level_sylow_of_primeLocal
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (M : Rep (ZMod p) (primeLocalGaloisGroup q)) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, primeLocalToGlobal q s ∈ F.fixingSubgroup → M.ρ s m = m) :
    ∃ (U S : Subgroup (primeLocalGaloisGroup q)),
      U ≤ S ∧ U.Normal ∧
      (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
        F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ U) ∧
      S.FiniteIndex ∧ IsUnit ((S.index : ℕ) : ZMod p) ∧
      (∀ s : primeLocalGaloisGroup q, s ∈ S → ∃ n : ℕ, s ^ (p ^ n) ∈ U) ∧
      (∀ u : primeLocalGaloisGroup q, u ∈ U → ∀ m : M, M.ρ u m = m) ∧
      (∀ u : primeLocalGaloisGroup q, u ∈ U → (cycloChar p) (primeLocalToGlobal q u) = 1) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_level_sylow_of_primeLocal.solution
