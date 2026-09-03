import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Topology.Instances.Matrix
import P2M.Util
import P2M.Sol.S_Matrix_GeneralLinearGroup_isMulRightInvariant_of_isHaarMeasure_fin_two

set_option autoImplicit false

open MeasureTheory Matrix

theorem Matrix.GeneralLinearGroup.isMulRightInvariant_of_isHaarMeasure_fin_two
    {F : Type*} [Field F] [CharZero F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace (GL (Fin 2) F)] [SecondCountableTopology (GL (Fin 2) F)]
    [MeasurableSpace (GL (Fin 2) F)] [BorelSpace (GL (Fin 2) F)]
    (μ : Measure (GL (Fin 2) F)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by p2m_exact_reverting @_root_.P2MW.S_Matrix_GeneralLinearGroup_isMulRightInvariant_of_isHaarMeasure_fin_two.solution
