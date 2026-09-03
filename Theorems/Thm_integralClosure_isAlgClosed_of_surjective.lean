import Mathlib
import P2M.Util
import P2M.Sol.S_integralClosure_isAlgClosed_of_surjective

set_option autoImplicit false

theorem integralClosure.isAlgClosed_of_surjective
    {R L F : Type*} [CommRing R] [Field L] [IsAlgClosed L] [Algebra R L] [Field F]
    (φ : integralClosure R L →+* F) (hφ : Function.Surjective φ) :
    IsAlgClosed F := by p2m_exact_reverting @_root_.P2MW.S_integralClosure_isAlgClosed_of_surjective.solution
