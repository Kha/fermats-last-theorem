import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_ExtCitation_LocalLevelSubgroupsPD
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import P2M.Util
import P2M.Sol.S_ExtCitation_finrank_le_of_levelBound_of_forall_iff_exists_rightInvariantRep

open CategoryTheory groupCohomology ExtCitation
theorem ExtCitation.finrank_le_of_levelBound_of_forall_iff_exists_rightInvariantRep (p : ℕ) [Fact p.Prime] (q : Nat.Primes) (M : Rep (ZMod p) (primeLocalGaloisGroup q)) [FiniteDimensional (ZMod p) M]
    (F₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F₀]
    (b : ℕ)
    (hlevel : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F → ∀ _ : Normal ℚ F, F₀ ≤ F →
      Module.finrank (ZMod p) (inflationImage M ((F.fixingSubgroup).comap (primeLocalToGlobal q))) ≤ b)
    (adm₁ : Submodule (ZMod p) (H1 M))
    (hadm₁ : ∀ x, x ∈ adm₁ ↔ ∃ c : cocycles₁ M, H1π M c = x ∧
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ g s : primeLocalGaloisGroup q, primeLocalToGlobal q s ∈ F.fixingSubgroup → c (g * s) = c g) :
    Module.finrank (ZMod p) adm₁ ≤ b := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_finrank_le_of_levelBound_of_forall_iff_exists_rightInvariantRep.solution
