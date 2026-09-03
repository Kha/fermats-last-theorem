import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_ringEquiv_functionField_pullback_of_closure_eq_top_of_linearIndependent

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap~exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd AlgebraicCurve"
open scoped TensorProduct

theorem AlgebraicGeometry.exists_ringEquiv_functionField_pullback_of_closure_eq_top_of_linearIndependent
    {R₀ : Type} [CommRing R₀] [Algebra R₀ ℚ]
    {X : Scheme.{0}} (πX : X ⟶ Spec (CommRingCat.of R₀)) [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsIntegral
      ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ)))))]
    (hinj : Function.Injective (algebraMap R₀ (AlgebraicClosure ℚ)))
    {F : Type} [Field F] [Algebra ℚ F] (eF : F ≃+* X.functionField)
    {Fbar : Type} [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar] (toBar : F →+* Fbar)
    (toBar_algebraMap : ∀ r : ℚ,
      toBar (algebraMap ℚ F r) = algebraMap (AlgebraicClosure ℚ) Fbar (algebraMap ℚ (AlgebraicClosure ℚ) r))
    (closure_toBar : Subfield.closure
      (Set.range (algebraMap (AlgebraicClosure ℚ) Fbar) ∪ Set.range toBar) = ⊤)
    (linearIndependent_toBar : ∀ s : Finset F,
      LinearIndependent ℚ (fun x : s => (x : F)) →
        LinearIndependent (AlgebraicClosure ℚ) (fun x : s => toBar (x : F)))

    (eF_symm_germ : ∀ r : R₀,
      eF.symm ((X.presheaf.germ ⊤ (genericPoint X) trivial).hom
        (πX.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom r))) =
      algebraMap ℚ F (algebraMap R₀ ℚ r)) :
    ∃ eFbar : Fbar ≃+* ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).functionField,
      (∀ z : AlgebraicClosure ℚ, eFbar (algebraMap (AlgebraicClosure ℚ) Fbar z) =
        baseToFunctionField (pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))) z) ∧
      ∀ (U : X.Opens) [Nonempty (U : Scheme.{0})]
        [Nonempty (((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))) ⁻¹ᵁ U :
          (pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).Opens) : Scheme.{0})]
        (t : Γ(X, U)),
        eFbar (toBar (eF.symm (X.germToFunctionField U t))) =
          (pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).germToFunctionField
            ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))) ⁻¹ᵁ U)
            ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).app U t) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_ringEquiv_functionField_pullback_of_closure_eq_top_of_linearIndependent.solution
