import Mathlib
import Definitions.Def_GroupCohomology_CyclicCarry
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_eq_d12_of_invariant_of_mul_dvd_orderOf

set_option autoImplicit false
open CategoryTheory groupCohomology
theorem groupCohomology.exists_eq_d12_of_invariant_of_mul_dvd_orderOf
    {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (p : ℕ) (hpA : ∀ a : A, p • a = 0)
    (N : Subgroup G) [N.Normal] (hN : ∀ n ∈ N, A.ρ n = 1)
    (φ : G) (hgen : ∀ g : G, ∃ i : ℕ, (φ ^ i)⁻¹ * g ∈ N)
    (hfin : IsOfFinOrder (QuotientGroup.mk φ : G ⧸ N))
    (e : ℕ) (hdiv : p * e ∣ orderOf (QuotientGroup.mk φ : G ⧸ N))
    (E : G × G → A) (hE : E ∈ cocycles₂ A)
    (hEe : ∀ g h : G, E (g * φ ^ e, h) = E (g, h))
    (hE₁ : ∀ g h n : G, n ∈ N → E (g * n, h) = E (g, h))
    (hE₂ : ∀ g h n : G, n ∈ N → E (g, h * n) = E (g, h)) :
    ∃ b : G → A, (∀ g n : G, n ∈ N → b (g * n) = b g) ∧
      ∀ g h : G, E (g, h) = A.ρ g (b h) - b (g * h) + b g := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_eq_d12_of_invariant_of_mul_dvd_orderOf.solution
