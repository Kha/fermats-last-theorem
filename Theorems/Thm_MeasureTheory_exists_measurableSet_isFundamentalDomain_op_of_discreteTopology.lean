import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Algebra.Group.Basic
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_measurableSet_isFundamentalDomain_op_of_discreteTopology

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_measurableSet_isFundamentalDomain_op_of_discreteTopology
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) (hΓ : DiscreteTopology Γ) :
    ∃ D : Set G, MeasurableSet D ∧ (∀ x : G, ∃! γ : Γ, x * (γ : G) ∈ D) ∧
      ∀ μ : Measure G, IsFundamentalDomain Γ.op D μ := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_measurableSet_isFundamentalDomain_op_of_discreteTopology.solution
