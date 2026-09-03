import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FinitePresentation_of_surjective_of_isNilpotent_ker_of_flat_of_finitePresentation

set_option autoImplicit false

universe u v w

theorem Algebra.FinitePresentation.of_surjective_of_isNilpotent_ker_of_flat_of_finitePresentation
    {P B' : Type u} [CommRing P] [CommRing B'] (p : P →+* B') (hp : Function.Surjective p)
    (hI : IsNilpotent (RingHom.ker p))
    {A : Type v} [CommRing A] [Algebra P A] [Module.Flat P A]
    {A' : Type w} [CommRing A'] [Algebra B' A']
    (q : A →+* A') (hq : Function.Surjective q)
    (hcomm : q.comp (algebraMap P A) = (algebraMap B' A').comp p)
    (hker : RingHom.ker q = (RingHom.ker p).map (algebraMap P A))
    (hfp' : Algebra.FinitePresentation B' A') :
    Algebra.FinitePresentation P A := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FinitePresentation_of_surjective_of_isNilpotent_ker_of_flat_of_finitePresentation.solution
