import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FiniteType_of_faithfullyFlat_of_finitePresentation

universe u v w

theorem Algebra.FiniteType.of_faithfullyFlat_of_finitePresentation
    (R : Type u) (A : Type v) (B : Type w) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Module.FaithfullyFlat A B] [Algebra.FinitePresentation A B] [Algebra.FiniteType R B] :
    Algebra.FiniteType R A := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FiniteType_of_faithfullyFlat_of_finitePresentation.solution
