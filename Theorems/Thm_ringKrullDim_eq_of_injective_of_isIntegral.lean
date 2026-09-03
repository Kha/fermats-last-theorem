import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import P2M.Util
import P2M.Sol.S_ringKrullDim_eq_of_injective_of_isIntegral

set_option autoImplicit false

theorem ringKrullDim_eq_of_injective_of_isIntegral
    (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
    (hinj : Function.Injective (algebraMap A B)) :
    ringKrullDim B = ringKrullDim A := by p2m_exact_reverting @_root_.P2MW.S_ringKrullDim_eq_of_injective_of_isIntegral.solution
