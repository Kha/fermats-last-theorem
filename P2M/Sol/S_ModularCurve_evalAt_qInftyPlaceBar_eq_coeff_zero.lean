import Mathlib
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Sol.S_ModularCurve_algebraMap_coeff_zero_sub_not_isUnit_bar
import Theorems.Thm_AlgebraicCurve_Place_mk_mem_maximalIdeal_iff
import P2M.Sol.S_AlgebraicCurve_Place_evalAt_congr
import P2M.Sol.S_AlgebraicCurve_Place_evalAt_algebraMap
import P2M.Util
namespace P2MW.S_ModularCurve_evalAt_qInftyPlaceBar_eq_coeff_zero
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem solution (L : Type*) [Field L]
    {F : IntermediateField L (LaurentSeries L)} (h : ∃ j : F, (qSeriesBar L F j).order = -1)
    (f : F) (hf : 0 ≤ (qSeriesBar L F f).order) :
    (qInftyPlaceBar L F h).evalAt f = (qSeriesBar L F f).coeff 0 := by
  set v := qInftyPlaceBar L F h with hv
  set c : L := (qSeriesBar L F f).coeff 0 with hc

  have hfmem : f ∈ v.toValuationSubring := by
    rw [hv, qInftyPlaceBar_toValuationSubring, mem_qIntegersBar_iff]
    exact hf
  have hcmem : algebraMap L F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hsub : algebraMap L F c - f ∈ v.toValuationSubring := sub_mem hcmem hfmem

  have hnu := algebraMap_coeff_zero_sub_not_isUnit_bar L h ⟨f, hfmem⟩
  have hmax : (⟨algebraMap L F c - f, hsub⟩ : v.toValuationSubring)
      ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    have e : (⟨algebraMap L F c - f, hsub⟩ : v.toValuationSubring)
        = algebraMap L v.toValuationSubring c - ⟨f, hfmem⟩ := by
      apply Subtype.ext
      rw [AddSubgroupClass.coe_sub, v.coe_algebraMap]
    rw [e, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hnu
  have hcong : algebraMap L F c - f = 0 ∨ 0 < v.ord (algebraMap L F c - f) :=
    (v.mk_mem_maximalIdeal_iff hsub).1 hmax
  calc v.evalAt f = v.evalAt (algebraMap L F c) := (v.evalAt_congr hcmem hfmem hcong).symm
    _ = c := v.evalAt_algebraMap c
