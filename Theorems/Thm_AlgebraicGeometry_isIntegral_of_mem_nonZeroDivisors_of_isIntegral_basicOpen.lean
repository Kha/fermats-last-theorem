import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIntegral_of_mem_nonZeroDivisors_of_isIntegral_basicOpen

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

theorem AlgebraicGeometry.isIntegral_of_mem_nonZeroDivisors_of_isIntegral_basicOpen {Y : Scheme} (p : Γ(Y, ⊤))
    (hreg : ∀ U : Y.Opens, IsAffineOpen U → Y.presheaf.map (homOfLE le_top).op p ∈ nonZeroDivisors Γ(Y, U))
    [hint : IsIntegral (Y.basicOpen p : Scheme)] : IsIntegral Y := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIntegral_of_mem_nonZeroDivisors_of_isIntegral_basicOpen.solution
