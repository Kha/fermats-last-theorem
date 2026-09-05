module

public import Definitions.Def_ModularCurve_QAdicPlace
public import Theorems.Thm_ModularCurve_surjective_algebraMap_residueField_bar
import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_deg_qInftyPlaceBar

open ModularCurve AlgebraicCurve

theorem solution (L : Type*) [Field L] {F : IntermediateField L (LaurentSeries L)} (h : ∃ j : F, (qSeriesBar L F j).order = -1) : (qInftyPlaceBar L F h).deg = 1 := by
  have hsurj := ModularCurve.surjective_algebraMap_residueField_bar L h
  have hinj : Function.Injective (algebraMap L (qInftyPlaceBar L F h).ResidueField) :=
    (algebraMap L (qInftyPlaceBar L F h).ResidueField).injective
  have e : L ≃ₐ[L] (qInftyPlaceBar L F h).ResidueField :=
    AlgEquiv.ofBijective (Algebra.ofId L _) ⟨hinj, hsurj⟩
  show Module.finrank L (qInftyPlaceBar L F h).ResidueField = 1
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]
