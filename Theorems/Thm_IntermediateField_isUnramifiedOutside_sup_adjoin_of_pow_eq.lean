import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import P2M.Util
import P2M.Sol.S_IntermediateField_isUnramifiedOutside_sup_adjoin_of_pow_eq

set_option autoImplicit false
theorem IntermediateField.isUnramifiedOutside_sup_adjoin_of_pow_eq
    (S : Finset Nat.Primes) (p : Nat.Primes) (hp : p ∈ S)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hF : F.IsUnramifiedOutside S)
    (x : AlgebraicClosure ℚ) (hxF : x ∈ F)
    (hxS : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (q : ℕ) → x ∈ A ∧ x⁻¹ ∈ A)
    (α : AlgebraicClosure ℚ) (hα : α ^ (p : ℕ) = x) :
    (F ⊔ IntermediateField.adjoin ℚ {α}).IsUnramifiedOutside S := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_isUnramifiedOutside_sup_adjoin_of_pow_eq.solution
