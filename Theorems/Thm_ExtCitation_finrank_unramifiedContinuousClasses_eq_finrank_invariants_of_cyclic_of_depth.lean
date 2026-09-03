import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ExtCitation_LocalLevelSubgroupsPD
import P2M.Util
import P2M.Sol.S_ExtCitation_finrank_unramifiedContinuousClasses_eq_finrank_invariants_of_cyclic_of_depth

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation
theorem ExtCitation.finrank_unramifiedContinuousClasses_eq_finrank_invariants_of_cyclic_of_depth
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (M : Rep (ZMod p) (primeLocalGaloisGroup q)) [FiniteDimensional (ZMod p) M]

    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ F ∧
        ∀ s, primeLocalToGlobal q s ∈ F.fixingSubgroup → M.ρ s m = m)

    (φ : primeLocalGaloisGroup q)
    (hcyc : ∀ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [Normal ℚ F],
      ∀ x : primeLocalGaloisGroup q ⧸
          ((((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)) ⊔
            ((F.fixingSubgroup).comap (primeLocalToGlobal q))),
        x ∈ Subgroup.zpowers (QuotientGroup.mk φ :  primeLocalGaloisGroup q ⧸
          ((((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)) ⊔
            ((F.fixingSubgroup).comap (primeLocalToGlobal q)))))

    (hdepth : ∀ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ → ∀ n : ℕ, 0 < n →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ Normal ℚ F ∧ F₀ ≤ F ∧
        ∀ j : ℕ, φ ^ j ∈ ((((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)) ⊔
            ((F.fixingSubgroup).comap (primeLocalToGlobal q))) → n ∣ j)

    (adm_ur : Submodule (ZMod p) (H1 M)) [FiniteDimensional (ZMod p) adm_ur]
    (hadm_ur : ∀ x, x ∈ adm_ur ↔ ∃ c : cocycles₁ M,
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ (g s : primeLocalGaloisGroup q),
          primeLocalToGlobal q s ∈ F.fixingSubgroup → c.val (g * s) = c.val g)
      ∧ (∃ m : M, ∀ g : primeLocalGaloisGroup q,
          primeLocalToGlobal q g ∈ (primeLocalPlace q).inertiaSubgroupIn ℚ → c.val g = M.ρ g m - m)
      ∧ (H1π M).hom c = x) :
    finrank (ZMod p) adm_ur = finrank (ZMod p) M.ρ.invariants := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_finrank_unramifiedContinuousClasses_eq_finrank_invariants_of_cyclic_of_depth.solution
