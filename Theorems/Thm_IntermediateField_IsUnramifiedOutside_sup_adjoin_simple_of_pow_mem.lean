import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import P2M.Util
import P2M.Sol.S_IntermediateField_IsUnramifiedOutside_sup_adjoin_simple_of_pow_mem

set_option autoImplicit false

theorem IntermediateField.IsUnramifiedOutside.sup_adjoin_simple_of_pow_mem
    (S : Finset Nat.Primes) {p : ℕ} (hp : p.Prime) (hpS : (⟨p, hp⟩ : Nat.Primes) ∈ S)
    {F : IntermediateField ℚ (AlgebraicClosure ℚ)} (hF : F.IsUnramifiedOutside S)
    {α : AlgebraicClosure ℚ} (hα : α ^ p ∈ F)
    (hαS : ∀ A : ValuationSubring (AlgebraicClosure ℚ), (∀ q ∈ S, ¬ A.LiesOverPrime ((q : Nat.Primes) : ℕ)) →
      α ^ p ∈ A ∧ (α ^ p)⁻¹ ∈ A) :
    (F ⊔ IntermediateField.adjoin ℚ {α}).IsUnramifiedOutside S := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_IsUnramifiedOutside_sup_adjoin_simple_of_pow_mem.solution
