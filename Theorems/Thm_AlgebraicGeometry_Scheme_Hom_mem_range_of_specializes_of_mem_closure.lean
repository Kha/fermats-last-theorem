import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_mem_range_of_specializes_of_mem_closure

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.Hom.mem_range_of_specializes_of_mem_closure
    {Γ G : Scheme.{u}} (π : Γ ⟶ G) [QuasiCompact π] [LocallyOfFiniteType π] [IsLocallyNoetherian G]
    (S : Set G) (hS : IsClosed S) (η : G) (hηS : η ∈ S) (hirr : ∀ x ∈ S, η ⤳ x)
    (D : Set G) (hDS : D ⊆ S) (hDη : η ∈ closure D) (hDπ : D ⊆ Set.range π.base) :
    η ∈ Set.range π.base := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_mem_range_of_specializes_of_mem_closure.solution
