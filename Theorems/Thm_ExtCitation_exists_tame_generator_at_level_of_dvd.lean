import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_ExtCitation_exists_tame_generator_at_level_of_dvd
attribute [-instance] ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete
attribute [-simp] ExtCitation.LocalLevel.coe_smul_OO

open ExtCitation
theorem ExtCitation.exists_tame_generator_at_level_of_dvd (q : Nat.Primes)
    (φ : primeLocalGaloisGroup q) (hφ : (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q)
    (F₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F₀]
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hqn : ¬ (q : ℕ) ∣ n) :
    ∃ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ F) (_ : IsGalois ℚ F),
      F₀ ≤ F ∧
      ∃ (t : primeLocalGaloisGroup q) (W : Subgroup (primeLocalGaloisGroup q)) (_ : W.Normal),
        t ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q) ∧
        (F.fixingSubgroup).comap (primeLocalToGlobal q) ≤ W ∧
        W ≤ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q) ⊔
              (F.fixingSubgroup).comap (primeLocalToGlobal q) ∧
        (∀ w ∈ W, ∃ a : ℕ, w ^ ((q : ℕ) ^ a) ∈ (F.fixingSubgroup).comap (primeLocalToGlobal q)) ∧
        (∀ i ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q), ∃ a : ℕ, (t ^ a)⁻¹ * i ∈ W) ∧
        (t ^ (q : ℕ))⁻¹ * (φ * t * φ⁻¹) ∈ W ∧
        IsOfFinOrder (QuotientGroup.mk t : primeLocalGaloisGroup q ⧸ W) ∧
        n ∣ orderOf (QuotientGroup.mk t : primeLocalGaloisGroup q ⧸ W) ∧
        ∃ (_ : (Subgroup.zpowers (QuotientGroup.mk t : primeLocalGaloisGroup q ⧸ W)).Normal),
          d ∣ orderOf (QuotientGroup.mk (QuotientGroup.mk φ : primeLocalGaloisGroup q ⧸ W) :
                (primeLocalGaloisGroup q ⧸ W) ⧸ Subgroup.zpowers (QuotientGroup.mk t : primeLocalGaloisGroup q ⧸ W)) ∧
          ∃ j : ℕ, n ∣ j ∧
            (QuotientGroup.mk φ : primeLocalGaloisGroup q ⧸ W) ^
                orderOf (QuotientGroup.mk (QuotientGroup.mk φ : primeLocalGaloisGroup q ⧸ W) :
                  (primeLocalGaloisGroup q ⧸ W) ⧸ Subgroup.zpowers (QuotientGroup.mk t : primeLocalGaloisGroup q ⧸ W))
              = (QuotientGroup.mk t : primeLocalGaloisGroup q ⧸ W) ^ j := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_exists_tame_generator_at_level_of_dvd.solution
