import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_ExtCitation_exists_tame_generator_at_level
attribute [-instance] ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal

open ExtCitation
theorem ExtCitation.exists_tame_generator_at_level (q : Nat.Primes)
    (φ : primeLocalGaloisGroup q) (hφ : (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [IsGalois ℚ F] :
    ∃ (t : primeLocalGaloisGroup q) (W : Subgroup (primeLocalGaloisGroup q)),
      t ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q) ∧
      (F.fixingSubgroup).comap (primeLocalToGlobal q) ≤ W ∧
      W ≤ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q) ⊔ (F.fixingSubgroup).comap (primeLocalToGlobal q) ∧
      W.Normal ∧
      (∀ w ∈ W, ∃ a : ℕ, w ^ ((q : ℕ) ^ a) ∈ (F.fixingSubgroup).comap (primeLocalToGlobal q)) ∧
      (∀ i ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q), ∃ a : ℕ, (t ^ a)⁻¹ * i ∈ W) ∧
      (t ^ (q : ℕ))⁻¹ * (φ * t * φ⁻¹) ∈ W := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_exists_tame_generator_at_level.solution
