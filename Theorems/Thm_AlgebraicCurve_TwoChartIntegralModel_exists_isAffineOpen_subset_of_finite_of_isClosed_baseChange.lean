import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_isAffineOpen_subset_of_finite_of_isClosed_baseChange
attribute [-instance] AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
attribute [-simp] AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.TwoChartIntegralModel.exists_isAffineOpen_subset_of_finite_of_isClosed_baseChange
    {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    {A : Type u} [CommRing A] [IsLocalRing A] [Infinite (IsLocalRing.ResidueField A)] (φ : R →+* A)
    (T : Set ↥(pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom φ))))
    (hT : T.Finite) (hTcl : ∀ t ∈ T, IsClosed ({t} : Set ↥(pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom φ))))) :
    ∃ U : (pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom φ))).Opens,
      IsAffineOpen U ∧ T ⊆ (U : Set ↥(pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom φ)))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_isAffineOpen_subset_of_finite_of_isClosed_baseChange.solution
