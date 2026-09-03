import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_of_finite_maximalSpectrum

set_option autoImplicit false

open MeasureTheory

theorem AutomorphicForm.isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_of_finite_maximalSpectrum
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [Finite (MaximalSpectrum A)]
    (μA : @Measure (GL (Fin 2) A) (AutomorphicForm.glBorelOf A))
    (hμA : @Measure.IsHaarMeasure (GL (Fin 2) A) _ _ (AutomorphicForm.glBorelOf A) μA) :
    @Measure.IsMulRightInvariant (GL (Fin 2) A) (AutomorphicForm.glBorelOf A) _ μA := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_of_finite_maximalSpectrum.solution
