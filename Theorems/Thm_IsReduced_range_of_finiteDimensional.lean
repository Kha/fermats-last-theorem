import Mathlib
import P2M.Util
import P2M.Sol.S_IsReduced_range_of_finiteDimensional
set_option autoImplicit false

theorem IsReduced.range_of_finiteDimensional
    {K A B : Type*} [Field K] [CommRing A] [Algebra K A] [FiniteDimensional K A] [IsReduced A] [Ring B] [Algebra K B]
    (f : A →ₐ[K] B) : IsReduced ↥f.range := by p2m_exact_reverting @_root_.P2MW.S_IsReduced_range_of_finiteDimensional.solution
