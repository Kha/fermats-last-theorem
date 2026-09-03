import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_UnitCocycle_exists_notMem_comap_eq_of_atPrime_of_isSeparated
attribute [-instance] TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp] AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

theorem AlgebraicGeometry.Scheme.Modules.UnitCocycle.exists_notMem_comap_eq_of_atPrime_of_isSeparated
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    [QuasiCompact f] [IsSeparated f] (𝔭 : Ideal S) [𝔭.IsPrime]
    {ι : Type u} [Finite ι] (W : ι → A.Opens) (hW : ∀ k, IsAffineOpen (W k))
    (hcov : (⨆ k, (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭))))) ⁻¹ᵁ W k) = ⊤)
    (g : Scheme.Modules.UnitCocycle fun k =>
      (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭))))) ⁻¹ᵁ W k) :
    ∃ (r : S) (_ : r ∉ 𝔭) (ψ : Localization.Away r →+* Localization.AtPrime 𝔭)
      (hψ : ψ.comp (algebraMap S (Localization.Away r)) = algebraMap S (Localization.AtPrime 𝔭))
      (c : Scheme.Modules.UnitCocycle fun k =>
        (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))) ⁻¹ᵁ W k),
      (⨆ k, (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))) ⁻¹ᵁ W k) = ⊤ ∧
      ∀ (i j : ι)
        (e : (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭))))) ⁻¹ᵁ W i ⊓
              (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭))))) ⁻¹ᵁ W j =
            (Limits.pullback.lift
                (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))))
                (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))) ≫
                  Spec.map (CommRingCat.ofHom ψ))
                (by rw [Limits.pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]) :
                Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))) ⟶
                  Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))) ⁻¹ᵁ
              ((Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))) ⁻¹ᵁ W i) ⊓
            (Limits.pullback.lift
                (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))))
                (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))) ≫
                  Spec.map (CommRingCat.ofHom ψ))
                (by rw [Limits.pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]) :
                Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))) ⟶
                  Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))) ⁻¹ᵁ
              ((Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))) ⁻¹ᵁ W j)),
        (Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭))))).presheaf.map
            (eqToHom e).op
            ((c.comap
              (Limits.pullback.lift
                (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))))
                (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))) ≫
                  Spec.map (CommRingCat.ofHom ψ))
                (by rw [Limits.pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]))).u i j) =
          g.u i j := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_UnitCocycle_exists_notMem_comap_eq_of_atPrime_of_isSeparated.solution
