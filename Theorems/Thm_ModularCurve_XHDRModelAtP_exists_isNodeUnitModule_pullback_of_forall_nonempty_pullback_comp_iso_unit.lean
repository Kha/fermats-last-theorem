import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule
import P2M.Util
import P2M.Sol.S_ModularCurve_XHDRModelAtP_exists_isNodeUnitModule_pullback_of_forall_nonempty_pullback_comp_iso_unit
attribute [-simp] AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.TwoGluedCurves
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_isNodeUnitModule_pullback_of_forall_nonempty_pullback_comp_iso_unit
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    letI : Algebra (R p) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
    ∀ (β : SchemeHomOver (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) (Spec.map (CommRingCat.ofHom ρ)))
      (_ : β.1 = resPt A)

      (hc : pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥A)) =
        pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥A)))

      [Finite (SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥A))))]
      (_ : Function.Injective fun j : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥A))) =>
        (j.1 ≫ pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (_ : ∀ (q₁ q₂ : ↥(pullback (toBase p (ΓN p M H hpM) hj) (specMap (R p) (ResidueField ↥A)))),
        (𝔛.comp A hA ρ hρ 0).base q₁ = (𝔛.comp A hA ρ hρ 1).base q₂ →
        ∃ j : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥A))), q₁ = (j.1 ≫ pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base (IsLocalRing.closedPoint (ResidueField ↥A)) ∧
          q₂ = (j.1 ≫ pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base (IsLocalRing.closedPoint (ResidueField ↥A)))

      (L : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Modules) (_ : Scheme.Modules.IsInvertible L)
      (_ : ∀ i : Fin 2, Nonempty ((Scheme.Modules.pullback (𝔛.comp A hA ρ hρ i ≫ baseChangeSnd (toBase p (ΓM M H) hj) β)).obj L ≅
        𝟙_ (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)).Modules)),
      ∃ u : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥A))) → Γ(Spec (CommRingCat.of (ResidueField ↥A)), ⊤)ˣ,
        IsNodeUnitModule (baseChange (R p) (toBase p (ΓM M H) hj) (ResidueField ↥A)) (⟨(𝔛.comp A hA ρ hρ 0), 𝔛.comp_over A hA ρ hρ 0⟩ : SchemeHomOver (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥A)) (baseChange (R p) (toBase p (ΓM M H) hj) (ResidueField ↥A))) (⟨(𝔛.comp A hA ρ hρ 1), 𝔛.comp_over A hA ρ hρ 1⟩ : SchemeHomOver (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥A)) (baseChange (R p) (toBase p (ΓM M H) hj) (ResidueField ↥A)))
          (fun j : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥A))) =>
            (⟨j.1 ≫ pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1), by rw [Category.assoc]; exact j.2⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥A))))
          (fun j : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥A))) =>
            (⟨j.1 ≫ pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1), by rw [Category.assoc, hc]; exact j.2⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥A))))
          (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) u
          ((Scheme.Modules.pullback (pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) (ResidueField ↥A)) (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) ≫
            baseChangeSnd (toBase p (ΓM M H) hj) β)).obj L) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XHDRModelAtP_exists_isNodeUnitModule_pullback_of_forall_nonempty_pullback_comp_iso_unit.solution
