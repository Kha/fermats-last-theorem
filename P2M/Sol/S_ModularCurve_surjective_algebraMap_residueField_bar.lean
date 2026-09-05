module

public import Definitions.Def_ModularCurve_QAdicPlace
import P2M.Sol.S_ModularCurve_algebraMap_coeff_zero_sub_not_isUnit_bar
import P2M.Util

namespace P2MW.S_ModularCurve_surjective_algebraMap_residueField_bar

open ModularCurve AlgebraicCurve

theorem solution (L : Type*) [Field L] {F : IntermediateField L (LaurentSeries L)} (h : ∃ j : F, (qSeriesBar L F j).order = -1) : Function.Surjective (algebraMap L (qInftyPlaceBar L F h).ResidueField) := by
  intro y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective
    (I := IsLocalRing.maximalIdeal (qInftyPlaceBar L F h).toValuationSubring) y
  refine ⟨(qSeriesBar L F (f : F)).coeff 0, ?_⟩
  have hmem : algebraMap L (qInftyPlaceBar L F h).toValuationSubring
      ((qSeriesBar L F (f : F)).coeff 0) - f ∈
      IsLocalRing.maximalIdeal (qInftyPlaceBar L F h).toValuationSubring := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact ModularCurve.algebraMap_coeff_zero_sub_not_isUnit_bar L h f
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem
    (I := IsLocalRing.maximalIdeal (qInftyPlaceBar L F h).toValuationSubring)
    (algebraMap L (qInftyPlaceBar L F h).toValuationSubring
      ((qSeriesBar L F (f : F)).coeff 0)) f).mpr hmem
end S_ModularCurve_surjective_algebraMap_residueField_bar
end P2MW

public section
open ModularCurve AlgebraicCurve

theorem ModularCurve.surjective_algebraMap_residueField_bar (L : Type*) [Field L] {F : IntermediateField L (LaurentSeries L)} (h : ∃ j : F, (qSeriesBar L F j).order = -1) : Function.Surjective (algebraMap L (qInftyPlaceBar L F h).ResidueField) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_surjective_algebraMap_residueField_bar.solution
end
