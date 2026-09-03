import Mathlib
import P2M.Util
import P2M.Sol.S_Module_isClosed_setOf_le_finrank_cohomology_baseChange_residueField_of_projective
attribute [-instance] TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp] TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.isClosed_setOf_le_finrank_cohomology_baseChange_residueField_of_projective
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)]
    [∀ i, Module.Finite R (K i)] [∀ i, Module.Projective R (K i)]
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hδδ : ∀ i, δ (i + 1) ∘ₗ δ i = 0) (r : ℕ) :
    IsClosed {q : PrimeSpectrum R | r ≤ Module.finrank q.asIdeal.ResidueField
        ↥(LinearMap.ker ((δ 0).baseChange q.asIdeal.ResidueField))} ∧
      ∀ i : ℕ, IsClosed {q : PrimeSpectrum R |
        r + Module.finrank q.asIdeal.ResidueField
            ↥((LinearMap.range ((δ i).baseChange q.asIdeal.ResidueField)).comap
              (LinearMap.ker ((δ (i + 1)).baseChange q.asIdeal.ResidueField)).subtype) ≤
          Module.finrank q.asIdeal.ResidueField
            ↥(LinearMap.ker ((δ (i + 1)).baseChange q.asIdeal.ResidueField))} := by p2m_exact_reverting @_root_.P2MW.S_Module_isClosed_setOf_le_finrank_cohomology_baseChange_residueField_of_projective.solution
