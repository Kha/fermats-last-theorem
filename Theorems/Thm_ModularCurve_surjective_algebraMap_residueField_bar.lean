import Definitions.Def_ModularCurve_QAdicPlace
import P2M.Util
import P2M.Sol.S_ModularCurve_surjective_algebraMap_residueField_bar

open ModularCurve AlgebraicCurve

theorem ModularCurve.surjective_algebraMap_residueField_bar (L : Type*) [Field L] {F : IntermediateField L (LaurentSeries L)} (h : ∃ j : F, (qSeriesBar L F j).order = -1) : Function.Surjective (algebraMap L (qInftyPlaceBar L F h).ResidueField) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_surjective_algebraMap_residueField_bar.solution
