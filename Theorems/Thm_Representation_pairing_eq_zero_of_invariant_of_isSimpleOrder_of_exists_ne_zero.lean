import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero

set_option autoImplicit false

theorem Representation.pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero
    {k : Type*} [CommSemiring k] {K : Type*} [Group K]
    {S : Type*} [AddCommMonoid S] [Module k S] {S' : Type*} [AddCommMonoid S'] [Module k S']
    {X : Type*} [AddCommMonoid X] [Module k X]
    (ρ : Representation k K S) (ρ' : Representation k K S') [IsSimpleOrder (Subrepresentation ρ')]
    (β : S →ₗ[k] S' →ₗ[k] X) (hβ : ∀ (g : K) (s : S) (s' : S'), β (ρ g s) (ρ' g s') = β s s')
    (h0 : ∃ s' : S', s' ≠ 0 ∧ ∀ s : S, β s s' = 0) :
    β = 0 := by p2m_exact_reverting @_root_.P2MW.S_Representation_pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero.solution
