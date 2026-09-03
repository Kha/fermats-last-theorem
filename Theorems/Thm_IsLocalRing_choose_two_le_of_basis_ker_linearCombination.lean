import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_choose_two_le_of_basis_ker_linearCombination

set_option autoImplicit false

open scoped BigOperators

theorem IsLocalRing.choose_two_le_of_basis_ker_linearCombination
    {R : Type} [CommRing R] [IsLocalRing R] {m : ℕ} (σ : Fin m → R)
    (hσ : ∀ c : Fin m → R, ∑ i, c i * σ i ∈ IsLocalRing.maximalIdeal R ^ 2 →
      ∀ i, c i ∈ IsLocalRing.maximalIdeal R)
    {ρ : ℕ} (η : Module.Basis (Fin ρ) R (LinearMap.ker (Fintype.linearCombination R σ))) :
    m.choose 2 ≤ ρ := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_choose_two_le_of_basis_ker_linearCombination.solution
