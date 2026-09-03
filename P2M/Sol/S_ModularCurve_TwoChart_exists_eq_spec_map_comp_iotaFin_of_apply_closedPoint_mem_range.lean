import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import P2M.Util
namespace P2MW.S_ModularCurve_TwoChart_exists_eq_spec_map_comp_iotaFin_of_apply_closedPoint_mem_range

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    (A : Type u) [CommRing A] (K : Type u) [Field K] [Algebra A K] (j : K) [Fact (j ≠ 0)]
    (O : Type u) [CommRing O] [IsLocalRing O]
    (ξ : Spec (CommRingCat.of O) ⟶ ModularCurve.TwoChartModel A K j)
    (hξ : ξ.base (IsLocalRing.closedPoint O) ∈ Set.range (ModularCurve.TwoChart.ιFin A K j).base) :
    ∃ ψ : ↥(ModularCurve.TwoChart.chartAlgFin A K j) →+* O,
      ξ = Spec.map (CommRingCat.ofHom ψ) ≫ ModularCurve.TwoChart.ιFin A K j := by

  have hrange : Set.range ξ.base ⊆ Set.range (ModularCurve.TwoChart.ιFin A K j).base := by
    rintro _ ⟨x, rfl⟩
    have hopen : IsOpen (ξ.base ⁻¹' Set.range (ModularCurve.TwoChart.ιFin A K j).base) :=
      ((ModularCurve.TwoChart.ιFin A K j).isOpenEmbedding.isOpen_range).preimage ξ.base.hom.continuous
    have hspec : x ⤳ IsLocalRing.closedPoint O := IsLocalRing.specializes_closedPoint x
    exact (hopen.stableUnderGeneralization hspec hξ : _)

  let g : Spec (CommRingCat.of O) ⟶ ModularCurve.TwoChart.XFin A K j :=
    IsOpenImmersion.lift (ModularCurve.TwoChart.ιFin A K j) ξ hrange
  have hg : g ≫ ModularCurve.TwoChart.ιFin A K j = ξ := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨φ, hφ⟩ := Spec.map_surjective g
  refine ⟨φ.hom, ?_⟩
  rw [← hg, ← hφ]
  rfl
