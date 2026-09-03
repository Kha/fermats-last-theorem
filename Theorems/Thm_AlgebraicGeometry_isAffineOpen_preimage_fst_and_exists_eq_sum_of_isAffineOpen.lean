import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isAffineOpen_preimage_fst_and_exists_eq_sum_of_isAffineOpen
attribute [-instance] TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp] AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
theorem AlgebraicGeometry.isAffineOpen_preimage_fst_and_exists_eq_sum_of_isAffineOpen
    {𝒪 C : Type} [CommRing 𝒪] [CommRing C] (φ : 𝒪 →+* C)
    {𝒳 : Scheme.{0}} (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪))
    (sC : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of 𝒪)) (hsC : sC = Spec.map (CommRingCat.ofHom φ))
    (V : 𝒳.Opens) (hV : IsAffineOpen V) :
    IsAffineOpen ((Limits.pullback.fst f sC) ⁻¹ᵁ V) ∧
    ∀ t : (Limits.pullback f sC).presheaf.obj (Opposite.op ((Limits.pullback.fst f sC) ⁻¹ᵁ V)),
      ∃ (m : ℕ) (a : Fin m → 𝒳.presheaf.obj (Opposite.op V)) (c : Fin m → C),
        t = ∑ i, ((Limits.pullback f sC).presheaf.map (homOfLE (le_top : (Limits.pullback.fst f sC) ⁻¹ᵁ V ≤ ⊤)).op).hom
              ((Limits.pullback.snd f sC).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (c i))) *
            ((Limits.pullback.fst f sC).app V).hom (a i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isAffineOpen_preimage_fst_and_exists_eq_sum_of_isAffineOpen.solution
