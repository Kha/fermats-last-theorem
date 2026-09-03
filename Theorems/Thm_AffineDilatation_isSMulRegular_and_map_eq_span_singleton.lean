import Mathlib
import Definitions.Def_RingTheory_AffineDilatation
import P2M.Util
import P2M.Sol.S_AffineDilatation_isSMulRegular_and_map_eq_span_singleton

set_option autoImplicit false

universe u

theorem AffineDilatation.isSMulRegular_and_map_eq_span_singleton
    {A : Type u} [CommRing A] (I : Ideal A) (a : A) (ha : a ∈ I) :
    IsSMulRegular (AffineDilatation.Ring I a) a ∧
      I.map (algebraMap A (AffineDilatation.Ring I a)) =
        Ideal.span {algebraMap A (AffineDilatation.Ring I a) a} := by p2m_exact_reverting @_root_.P2MW.S_AffineDilatation_isSMulRegular_and_map_eq_span_singleton.solution
