import Mathlib
import P2M.Util
import P2M.Sol.S_Subgroup_commutatorElement_eq_and_mul_and_pow_of_forall_commutatorElement_mem_of_le_center

set_option autoImplicit false

open scoped commutatorElement

theorem Subgroup.commutatorElement_eq_and_mul_and_pow_of_forall_commutatorElement_mem_of_le_center
    {G : Type*} [Group G] (Z : Subgroup G) (hZ : Z ≤ Subgroup.center G)
    (hcomm : ∀ g h : G, ⁅g, h⁆ ∈ Z) :
    (∀ g g' h h' : G, g⁻¹ * g' ∈ Z → h⁻¹ * h' ∈ Z → ⁅g, h⁆ = ⁅g', h'⁆) ∧
    (∀ g g' h : G, ⁅g * g', h⁆ = ⁅g, h⁆ * ⁅g', h⁆) ∧
    (∀ g h h' : G, ⁅g, h * h'⁆ = ⁅g, h⁆ * ⁅g, h'⁆) ∧
    (∀ g h : G, ⁅g, h⁆ * ⁅h, g⁆ = 1) ∧
    (∀ g : G, ⁅g, g⁆ = 1) ∧
    (∀ (g h : G) (n : ℕ), ⁅g ^ n, h⁆ = ⁅g, h⁆ ^ n ∧ ⁅g, h ^ n⁆ = ⁅g, h⁆ ^ n) := by p2m_exact_reverting @_root_.P2MW.S_Subgroup_commutatorElement_eq_and_mul_and_pow_of_forall_commutatorElement_mem_of_le_center.solution
