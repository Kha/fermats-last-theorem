import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_Completion_Finite
import P2M.Util
import P2M.Sol.S_AutomorphicForm_secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory Topology

theorem AutomorphicForm.secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom
    (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    SecondCountableTopology (GL (Fin 2) (v.adicCompletion K)) ∧
    LocallyCompactSpace (GL (Fin 2) (v.adicCompletion K)) ∧
    IsClosed ((unipotentGL2Hom (R := v.adicCompletion K)).range : Set (GL (Fin 2) (v.adicCompletion K))) ∧
    (∀ {_m : MeasurableSpace ↥(unipotentGL2Hom (R := v.adicCompletion K)).range}
      (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion K)).range) [μN.IsMulLeftInvariant],
      μN.IsMulRightInvariant) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom.solution
