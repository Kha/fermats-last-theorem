import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isReduced_of_mem_nonZeroDivisors_of_isReduced_basicOpen
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite

theorem AlgebraicGeometry.isReduced_of_mem_nonZeroDivisors_of_isReduced_basicOpen
    {Y : Scheme} (p : Γ(Y, ⊤))
    (hreg : ∀ U : Y.Opens, IsAffineOpen U → Y.presheaf.map (homOfLE le_top).op p ∈ nonZeroDivisors Γ(Y, U))
    [IsReduced (Y.basicOpen p : Scheme)] : IsReduced Y := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isReduced_of_mem_nonZeroDivisors_of_isReduced_basicOpen.solution
