import Mathlib
import Definitions.Def_AlgebraicGeometry_MumfordTruncation
import P2M.Util
import P2M.Sol.S_Module_exists_mumfordTruncation_of_flat_complex
attribute [-instance] TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp] TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq

universe u

open TensorProduct

theorem Module.exists_mumfordTruncation_of_flat_complex
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbdd : ∀ i, n < i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0)))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype)) :
    ∃ (m₀ m₁ : ℕ) (P : Submodule R (C 0 × (Fin m₀ → R))) (ε : (Fin m₀ → R) →ₗ[R] (Fin m₁ → R)),
      Module.Finite R P ∧ Module.Flat R P ∧
      ε ∘ₗ (LinearMap.snd R (C 0) (Fin m₀ → R) ∘ₗ P.subtype) = 0 ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        (LinearMap.ker ((d 1).baseChange A) ≤ LinearMap.range ((d 0).baseChange A) →
          LinearMap.ker (ε.baseChange A)
            ≤ LinearMap.range ((LinearMap.snd R (C 0) (Fin m₀ → R) ∘ₗ P.subtype).baseChange A)) ∧
        (LinearMap.range ((LinearMap.ker (LinearMap.snd R (C 0) (Fin m₀ → R) ∘ₗ P.subtype)).subtype.baseChange A)
            = LinearMap.ker ((LinearMap.snd R (C 0) (Fin m₀ → R) ∘ₗ P.subtype).baseChange A) →
          LinearMap.range ((LinearMap.ker (d 0)).subtype.baseChange A) = LinearMap.ker ((d 0).baseChange A)) ∧
        (Function.Injective
            ((LinearMap.ker (LinearMap.snd R (C 0) (Fin m₀ → R) ∘ₗ P.subtype)).subtype.baseChange A) →
          Function.Injective ((LinearMap.ker (d 0)).subtype.baseChange A)) := by p2m_exact_reverting @_root_.P2MW.S_Module_exists_mumfordTruncation_of_flat_complex.solution
