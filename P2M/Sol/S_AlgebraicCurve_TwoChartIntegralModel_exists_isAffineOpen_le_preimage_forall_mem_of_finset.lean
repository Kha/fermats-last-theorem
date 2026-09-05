import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_isAffineOpen_forall_mem_of_finset
import Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_opens_le_preimage_forall_mem_of_forall_finset
import P2M.Util
namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_isAffineOpen_le_preimage_forall_mem_of_finset
attribute [-instance] AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
attribute [-simp] AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

universe u

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (U : (AlgebraicCurve.TwoChartIntegralModel R F j).Opens)
    (V : (Spec (CommRingCat.of R)).affineOpens) (S : Finset ↥U)
    (hS : ∀ x ∈ S, (U.ι ≫ toBase R F j).base x ∈ (V : (Spec (CommRingCat.of R)).Opens)) :
    ∃ W : (U : Scheme.{u}).Opens, IsAffineOpen W ∧
      W ≤ (U.ι ≫ toBase R F j) ⁻¹ᵁ (V : (Spec (CommRingCat.of R)).Opens) ∧ ∀ x ∈ S, x ∈ W := by
  exact AlgebraicGeometry.exists_isAffineOpen_opens_le_preimage_forall_mem_of_forall_finset
    (AlgebraicCurve.TwoChartIntegralModel.exists_isAffineOpen_forall_mem_of_finset R F j) U
    ((toBase R F j) ⁻¹ᵁ (V : (Spec (CommRingCat.of R)).Opens)) S hS

