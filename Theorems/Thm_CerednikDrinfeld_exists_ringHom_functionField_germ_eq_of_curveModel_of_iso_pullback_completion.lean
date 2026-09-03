import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ValuationSubring_CompletionRatClosure
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_exists_ringHom_functionField_germ_eq_of_curveModel_of_iso_pullback_completion
attribute [-instance] TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp] AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000

open CategoryTheory open AlgebraicGeometry hiding functionField_pullback_generates_and_linearIndependent

theorem CerednikDrinfeld.exists_ringHom_functionField_germ_eq_of_curveModel_of_iso_pullback_completion
    (R : Type) [CommRing R]
    (A₂ : ValuationSubring (AlgebraicClosure ℚ))
    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of R))
    (sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of R))

    (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) Fbar)
    (e𝔐 : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX sbar) [CategoryTheory.IsIso e𝔐]
    (he𝔐 : e𝔐 ≫ CategoryTheory.Limits.pullback.snd πX sbar = 𝔐.toBase)

    (𝒪₀ : Type) [CommRing 𝒪₀] [Algebra 𝒪₀ ↥(ValuationSubring.ratClosure A₂)]
    (𝒳₀ : Scheme.{0}) (f₀ : 𝒳₀ ⟶ Spec (CommRingCat.of 𝒪₀))
    [hXCint : IsIntegral (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))]

    (u : (Limits.pullback πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₂.valuation).symm.toRingHom))) ≫ sbar)) ≅ (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))))
    (hu : u.hom ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₂.valuation).symm.toRingHom))) ≫ sbar))
    :
    ∃ j : Fbar →+* ↑(Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).functionField,

      (∀ (x : Fbar) (U : 𝔐.C.Opens) (hU : (genericPoint (𝔐.C : Scheme.{0})) ∈ U)
        (hU' : (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) ∈ (u.inv ≫ Limits.pullback.lift (Limits.pullback.fst πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₂.valuation).symm.toRingHom))) ≫ sbar)) (Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₂.valuation).symm.toRingHom))) ≫ sbar) ≫ Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₂.valuation).symm.toRingHom)))) (by simp only [Category.assoc, Limits.pullback.condition]) ≫ CategoryTheory.inv e𝔐) ⁻¹ᵁ U)
        (sec : 𝔐.C.presheaf.obj (Opposite.op U)),
        (𝔐.C.presheaf.germ U (genericPoint (𝔐.C : Scheme.{0})) hU).hom sec = 𝔐.ffEquiv x →
        ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ ((u.inv ≫ Limits.pullback.lift (Limits.pullback.fst πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₂.valuation).symm.toRingHom))) ≫ sbar)) (Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₂.valuation).symm.toRingHom))) ≫ sbar) ≫ Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₂.valuation).symm.toRingHom)))) (by simp only [Category.assoc, Limits.pullback.condition]) ≫ CategoryTheory.inv e𝔐) ⁻¹ᵁ U) (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) hU').hom (((u.inv ≫ Limits.pullback.lift (Limits.pullback.fst πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₂.valuation).symm.toRingHom))) ≫ sbar)) (Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₂.valuation).symm.toRingHom))) ≫ sbar) ≫ Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₂.valuation).symm.toRingHom)))) (by simp only [Category.assoc, Limits.pullback.condition]) ≫ CategoryTheory.inv e𝔐).app U).hom sec) = j x) ∧

      (∀ z : AlgebraicClosure ℚ, j (algebraMap (AlgebraicClosure ℚ) Fbar z) = (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))) ((z : AlgebraicClosure ℚ) : A₂.valuation.Completion)) ∧

      (Subfield.closure (Set.range (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))) ∪ Set.range j) = ⊤) ∧

      (∀ (t : Finset Fbar), LinearIndependent (AlgebraicClosure ℚ) (fun x : t => (x : Fbar)) →
        ∀ c : t → A₂.valuation.Completion, (∑ x : t, (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))) (c x) * j (x : Fbar)) = 0 → ∀ x : t, c x = 0) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_exists_ringHom_functionField_germ_eq_of_curveModel_of_iso_pullback_completion.solution
