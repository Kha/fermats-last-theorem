import Definitions.Def_ExtEndgame_ProductionDatum
import P2M.Util
import P2M.Sol.S_ExtCitation_exists_padicLevel_fixingSubgroup_le_of_smooth
attribute [-instance] groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation
theorem ExtCitation.exists_padicLevel_fixingSubgroup_le_of_smooth
    (p : ℕ) [Fact p.Prime] (q : Nat.Primes) [Fact (q : ℕ).Prime]
    (S : Subgroup (primeLocalGaloisGroup q))
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S)
    {k : Type} [CommRing k] (N : Rep k S) [Module.Finite k N]
    (hsm : ∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → N.ρ s n = n) :
    ∃ K : IntermediateField ℚ_[(q : ℕ)] (PadicAlgCl (q : ℕ)), FiniteDimensional ℚ_[(q : ℕ)] K ∧
      (∃ ζ : K, IsPrimitiveRoot ζ p) ∧
      (∃ F₁ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₁ ∧
        F₁.fixingSubgroup.comap (primeLocalToGlobal q) ≤ K.fixingSubgroup) ∧
      (K.fixingSubgroup : Subgroup (primeLocalGaloisGroup q)).FiniteIndex ∧
      (∀ s : primeLocalGaloisGroup q, s ∈ K.fixingSubgroup → s ∈ S) ∧
      (∀ s : S, (s : primeLocalGaloisGroup q) ∈ K.fixingSubgroup → ∀ n : N, N.ρ s n = n) := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_exists_padicLevel_fixingSubgroup_le_of_smooth.solution
