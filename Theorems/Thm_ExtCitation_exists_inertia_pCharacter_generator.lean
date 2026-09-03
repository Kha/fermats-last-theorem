import Mathlib
import Definitions.Def_ExtCitation_InertiaKummerCharacter
import P2M.Util
import P2M.Sol.S_ExtCitation_exists_inertia_pCharacter_generator
attribute [-instance] instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO
attribute [-simp] ExtCitation.LocalLevel.coe_smul_OO

open ExtCitation
theorem ExtCitation.exists_inertia_pCharacter_generator (p : ℕ) [Fact p.Prime] (q : Nat.Primes) (hqp : (q : ℕ) ≠ p)
    (φ : primeLocalGaloisGroup q) (hφ : (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q) :
    ∃ (t : primeLocalGaloisGroup q)
      (ht : t ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q))
      (hφt : φ * t * φ⁻¹ ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)),
      ∀ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [IsGalois ℚ F]
        (χ : ↥(((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)) →* Multiplicative (ZMod p)),
        (∀ i : ↥(((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)),
          primeLocalToGlobal q (i : primeLocalGaloisGroup q) ∈ F.fixingSubgroup → χ i = 1) →
          (χ ⟨t, ht⟩ = 1 → χ = 1) ∧ χ ⟨φ * t * φ⁻¹, hφt⟩ = χ ⟨t, ht⟩ ^ (q : ℕ) := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_exists_inertia_pCharacter_generator.solution
