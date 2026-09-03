import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CurveModel_exists_ringHom_functionField_ffEquiv_symm_stalkMap_eq_of_isIso_pullback

set_option autoImplicit false

universe u v

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap"

theorem AlgebraicCurve.CurveModel.exists_ringHom_functionField_ffEquiv_symm_stalkMap_eq_of_isIso_pullback
    {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K))
    {L : Type v} [Field L] [Algebra K L] (M : AlgebraicCurve.CurveModel K L)
    {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of R))
    (e₀ : M.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M.toBase) :
    ∃ Θ : X.functionField →+* L,
      (∀ (P : X) (hgenP : (e₀ ≫ pullback.fst c _).base (genericPoint M.C) ⤳ P) (z : X.presheaf.stalk P),
        M.ffEquiv.symm ((Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c _) (genericPoint M.C)).hom
          ((X.presheaf.stalkSpecializes hgenP).hom z)) = Θ (algebraMap (X.presheaf.stalk P) X.functionField z)) ∧
      (∀ (x : M.C) (w : X.presheaf.stalk ((e₀ ≫ pullback.fst c _).base x)),
        M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x) M.C.functionField
          ((Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c _) x).hom w)) =
          Θ (algebraMap (X.presheaf.stalk ((e₀ ≫ pullback.fst c _).base x)) X.functionField w)) ∧
      (∀ (P : X) (r : R), Θ (algebraMap (X.presheaf.stalk P) X.functionField
          ((X.presheaf.germ ⊤ P trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)))) =
        algebraMap K L (algebraMap R K r)) ∧
      (IsIso (Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c _) (genericPoint M.C)) → Function.Bijective Θ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_exists_ringHom_functionField_ffEquiv_symm_stalkMap_eq_of_isIso_pullback.solution
