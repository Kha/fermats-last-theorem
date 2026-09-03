import Mathlib
import Definitions.Def_RingTheory_AffineDilatation
import P2M.Util
import P2M.Sol.S_AffineDilatation_nonempty_algHom_and_subsingleton_of_isSMulRegular

set_option autoImplicit false

universe u v

theorem AffineDilatation.nonempty_algHom_and_subsingleton_of_isSMulRegular
    {A : Type u} [CommRing A] (I : Ideal A) (a : A)
    {C : Type v} [CommRing C] [Algebra A C] (hreg : IsSMulRegular C a)
    (hI : I.map (algebraMap A C) ≤ Ideal.span {algebraMap A C a}) :
    Nonempty (AffineDilatation.Ring I a →ₐ[A] C) ∧
      Subsingleton (AffineDilatation.Ring I a →ₐ[A] C) := by p2m_exact_reverting @_root_.P2MW.S_AffineDilatation_nonempty_algHom_and_subsingleton_of_isSMulRegular.solution
