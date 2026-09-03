import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_IsAlgebraic_adjoin_singleton_of_finiteDimensional_intermediateField_adjoin_of_isFractionRing

set_option autoImplicit false

universe u

theorem Algebra.IsAlgebraic.adjoin_singleton_of_finiteDimensional_intermediateField_adjoin_of_isFractionRing
    (R : Type u) [CommRing R] [IsDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (F : Type u) [Field F] [Algebra R F] [Algebra K F] [IsScalarTower R K F]
    (g : F) (hFD : FiniteDimensional ↥(IntermediateField.adjoin K ({g} : Set F)) F) :
    Algebra.IsAlgebraic ↥(Algebra.adjoin R ({g} : Set F)) F := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsAlgebraic_adjoin_singleton_of_finiteDimensional_intermediateField_adjoin_of_isFractionRing.solution
