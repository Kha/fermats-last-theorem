import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FinitePresentation_of_faithfullyFlat_of_finitePresentation

set_option autoImplicit false

universe u v w

open TensorProduct

theorem Algebra.FinitePresentation.of_faithfullyFlat_of_finitePresentation
    (R : Type u) (A : Type v) (B : Type w) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Module.FaithfullyFlat A B] [Algebra.FinitePresentation A B] [Algebra.FinitePresentation R B] :
    Algebra.FinitePresentation R A := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FinitePresentation_of_faithfullyFlat_of_finitePresentation.solution
