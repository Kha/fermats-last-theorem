import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_finitePresentation_of_finite_of_flat_of_isLocalRing

set_option autoImplicit false

universe u v

theorem Algebra.finitePresentation_of_finite_of_flat_of_isLocalRing
    {R : Type u} [CommRing R] [IsLocalRing R] (C : Type v) [CommRing C] [Algebra R C]
    [Module.Finite R C] [Module.Flat R C] :
    Algebra.FinitePresentation R C := by p2m_exact_reverting @_root_.P2MW.S_Algebra_finitePresentation_of_finite_of_flat_of_isLocalRing.solution
