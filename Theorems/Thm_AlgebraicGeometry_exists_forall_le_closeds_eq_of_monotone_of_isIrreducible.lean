import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_forall_le_closeds_eq_of_monotone_of_isIrreducible

universe u v

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_forall_le_closeds_eq_of_monotone_of_isIrreducible
    {X : Scheme.{u}} [IsLocallyNoetherian X] (x : X) {ι : Type v} [Preorder ι] [Nonempty ι]
    (Z : ι → TopologicalSpace.Closeds X) (hZ : ∀ i, IsIrreducible (Z i : Set X)) (hx : ∀ i, x ∈ Z i)
    (hmono : Monotone Z) :
    ∃ i₀ : ι, ∀ i : ι, i₀ ≤ i → Z i = Z i₀ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_forall_le_closeds_eq_of_monotone_of_isIrreducible.solution
