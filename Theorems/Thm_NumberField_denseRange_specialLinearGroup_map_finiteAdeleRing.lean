import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Topology.Algebra.Group.Matrix
import P2M.Util
import P2M.Sol.S_NumberField_denseRange_specialLinearGroup_map_finiteAdeleRing
attribute [-instance] NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion
attribute [-simp] NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply

open IsDedekindDomain NumberField

theorem NumberField.denseRange_specialLinearGroup_map_finiteAdeleRing
    (F : Type) [Field F] [NumberField F] :
    DenseRange (Matrix.SpecialLinearGroup.map (n := Fin 2)
      (algebraMap F (FiniteAdeleRing (𝓞 F) F))) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_denseRange_specialLinearGroup_map_finiteAdeleRing.solution
