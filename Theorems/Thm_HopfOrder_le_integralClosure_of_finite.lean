import Mathlib
import P2M.Util
import P2M.Sol.S_HopfOrder_le_integralClosure_of_finite

universe u w
theorem HopfOrder.le_integralClosure_of_finite
    {R : Type u} [CommRing R] {A : Type w} [CommRing A] [Algebra R A]
    (S : Subalgebra R A) [Module.Finite R S] : S ≤ integralClosure R A := by p2m_exact_reverting @_root_.P2MW.S_HopfOrder_le_integralClosure_of_finite.solution
