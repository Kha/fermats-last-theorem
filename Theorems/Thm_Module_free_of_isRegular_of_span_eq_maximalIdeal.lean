import Mathlib
import P2M.Util
import P2M.Sol.S_Module_free_of_isRegular_of_span_eq_maximalIdeal

set_option autoImplicit false

theorem Module.free_of_isRegular_of_span_eq_maximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (rs : List A) (hA : RingTheory.Sequence.IsRegular A rs) (hspan : Ideal.ofList rs = IsLocalRing.maximalIdeal A)
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] (hM : RingTheory.Sequence.IsRegular M rs) :
    Module.Free A M := by p2m_exact_reverting @_root_.P2MW.S_Module_free_of_isRegular_of_span_eq_maximalIdeal.solution
