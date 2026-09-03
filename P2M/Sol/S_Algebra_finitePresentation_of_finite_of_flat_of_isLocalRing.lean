import Mathlib
import P2M.Util
namespace P2MW.S_Algebra_finitePresentation_of_finite_of_flat_of_isLocalRing

set_option autoImplicit false

universe u v

theorem solution
    {R : Type u} [CommRing R] [IsLocalRing R] (C : Type v) [CommRing C] [Algebra R C]
    [Module.Finite R C] [Module.Flat R C] :
    Algebra.FinitePresentation R C := by
  haveI : Module.Free R C := Module.free_of_flat_of_isLocalRing
  haveI : Module.FinitePresentation R C := Module.finitePresentation_of_projective R C
  exact Algebra.FinitePresentation.of_finitePresentation R C
