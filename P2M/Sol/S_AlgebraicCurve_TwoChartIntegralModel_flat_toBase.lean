import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.AlgebraicGeometry.Properties
import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_flat_toBase

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel"
namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "chartAlg XFin XInf ιFin ιInf isOpenImmersion_ιFin isOpenImmersion_ιInf toBase ιFin_toBase ιInf_toBase mem_range_ιFin_or_mem_range_ιInf"
p2m_open "AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

section Flat

variable [IsDomain R] [IsDedekindDomain R]

omit [Fact (j ≠ 0)] in
theorem isTorsionFree_of_injective (hinj : Function.Injective (algebraMap R F)) :
    Module.IsTorsionFree R F :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr hinj

omit [Fact (j ≠ 0)] in

theorem flat_chartAlg (hinj : Function.Injective (algebraMap R F)) (S : Set F) :
    Module.Flat R (chartAlg R F S) := by
  haveI := isTorsionFree_of_injective R F hinj
  haveI : Module.IsTorsionFree R (chartAlg R F S) := inferInstance
  infer_instance

omit [Fact (j ≠ 0)] in
theorem flat_specMap_chartAlg (hinj : Function.Injective (algebraMap R F)) (S : Set F) :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap R (chartAlg R F S)))) := by
  haveI := flat_chartAlg R F hinj S
  rw [HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
  infer_instance

noncomputable def twoChartOpenCover : (AlgebraicCurve.TwoChartIntegralModel R F j).OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun b => bif b then XFin R F j else XInf R F j)
    (fun b => match b with
      | true => ιFin R F j
      | false => ιInf R F j)
    (fun x => by
      rcases mem_range_ιFin_or_mem_range_ιInf R F j x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact ⟨true, y, hy⟩
      · exact ⟨false, y, hy⟩)
    (fun b => by
      cases b
      · exact isOpenImmersion_ιInf R F j
      · exact isOpenImmersion_ιFin R F j)

theorem flat_toBase_impl (hinj : Function.Injective (algebraMap R F)) : Flat (toBase R F j) := by
  refine IsZariskiLocalAtSource.of_openCover (P := @Flat) (twoChartOpenCover R F j) fun b => ?_
  cases b
  · show Flat (ιInf R F j ≫ toBase R F j)
    rw [ιInf_toBase]
    exact flat_specMap_chartAlg R F hinj _
  · show Flat (ιFin R F j ≫ toBase R F j)
    rw [ιFin_toBase]
    exact flat_specMap_chartAlg R F hinj _

end Flat

end AlgebraicCurve.TwoChartIntegralModel

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry _root_.AlgebraicCurve.TwoChartIntegralModel _root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_flat_toBase.AlgebraicCurve.TwoChartIntegralModel in
theorem solution.{u} (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    [IsDomain R] [IsDedekindDomain R] (hinj : Function.Injective (algebraMap R F)) :
    Flat (toBase R F j) :=
  AlgebraicCurve.TwoChartIntegralModel.flat_toBase_impl R F j hinj
