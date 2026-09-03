import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Conj
import Mathlib.GroupTheory.Commutator.Basic
import P2M.Util
import P2M.Sol.S_Ihara_ker_inf_commutator_eq_bot_of_dicyclic_closure_pair

open Subgroup in
theorem Ihara.ker_inf_commutator_eq_bot_of_dicyclic_closure_pair {G : Type*} [Group G] {a b : G}
    {t : ℕ} (hconj : b * a * b⁻¹ = a⁻¹) (hsq : b ^ 2 = a ^ t) (hord : orderOf a = 2 * t)
    {E : Type*} [Group E] (π : E →* closure ({a, b} : Set G)) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ center E) : π.ker ⊓ commutator E = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_Ihara_ker_inf_commutator_eq_bot_of_dicyclic_closure_pair.solution
