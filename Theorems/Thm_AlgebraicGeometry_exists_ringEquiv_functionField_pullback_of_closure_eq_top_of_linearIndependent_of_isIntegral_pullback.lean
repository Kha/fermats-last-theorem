import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_ringEquiv_functionField_pullback_of_closure_eq_top_of_linearIndependent_of_isIntegral_pullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open scoped TensorProduct

theorem AlgebraicGeometry.exists_ringEquiv_functionField_pullback_of_closure_eq_top_of_linearIndependent_of_isIntegral_pullback
    {K : Type} [Field K] {K' : Type} [Field K'] [Algebra K K']
    {X : Scheme.{0}} (πX : X ⟶ Spec (CommRingCat.of K)) [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsIntegral
      ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K'))))]
    {F : Type} [Field F] [Algebra K F] (eF : F ≃+* X.functionField)

    (eF_algebraMap : ∀ a : K, eF (algebraMap K F a) = baseToFunctionField πX a)
    {F' : Type} [Field F'] [Algebra K' F'] (to' : F →+* F')
    (to'_algebraMap : ∀ a : K,
      to' (algebraMap K F a) = algebraMap K' F' (algebraMap K K' a))
    (closure_to' : Subfield.closure
      (Set.range (algebraMap K' F') ∪ Set.range to') = ⊤)
    (linearIndependent_to' : ∀ s : Finset F,
      LinearIndependent K (fun x : s => (x : F)) →
        LinearIndependent K' (fun x : s => to' (x : F))) :
    ∃ eF' : F' ≃+* ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).functionField,
      (∀ z : K', eF' (algebraMap K' F' z) =
        baseToFunctionField (pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))) z) ∧
      ∀ (U : X.Opens) [Nonempty (U : Scheme.{0})]
        [Nonempty (((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ⁻¹ᵁ U :
          (pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).Opens) : Scheme.{0})]
        (t : Γ(X, U)),
        eF' (to' (eF.symm (X.germToFunctionField U t))) =
          (pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).germToFunctionField
            ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ⁻¹ᵁ U)
            ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).app U t) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_ringEquiv_functionField_pullback_of_closure_eq_top_of_linearIndependent_of_isIntegral_pullback.solution
