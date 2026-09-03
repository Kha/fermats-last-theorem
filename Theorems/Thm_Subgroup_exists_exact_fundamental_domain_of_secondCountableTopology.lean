import Mathlib.Topology.Algebra.Group.Basic
import P2M.Util
import P2M.Sol.S_Subgroup_exists_exact_fundamental_domain_of_secondCountableTopology

set_option autoImplicit false

theorem Subgroup.exists_exact_fundamental_domain_of_secondCountableTopology
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    (Γ : Subgroup G) (hdisc : ∃ V : Set G, IsOpen V ∧ V ∩ (Γ : Set G) = {1}) :
    ∃ F : Set G,
      (∃ U C : ℕ → Set G, (∀ n, IsOpen (U n)) ∧ (∀ n, IsOpen (C n)) ∧ F = ⋃ n, U n \ C n) ∧
      ∀ x : G, ∃! γ : ↥Γ, (γ : G) * x ∈ F := by p2m_exact_reverting @_root_.P2MW.S_Subgroup_exists_exact_fundamental_domain_of_secondCountableTopology.solution
