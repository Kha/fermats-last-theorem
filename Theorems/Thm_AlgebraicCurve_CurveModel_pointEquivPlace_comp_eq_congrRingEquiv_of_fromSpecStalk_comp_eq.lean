import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CurveModel_pointEquivPlace_comp_eq_congrRingEquiv_of_fromSpecStalk_comp_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u v

theorem AlgebraicCurve.CurveModel.pointEquivPlace_comp_eq_congrRingEquiv_of_fromSpecStalk_comp_eq
    {K : Type u} [Field K] [IsAlgClosed K]
    {L₁ : Type v} [Field L₁] [Algebra K L₁] {L₂ : Type v} [Field L₂] [Algebra K L₂]
    (M₁ : CurveModel K L₁) (M₂ : CurveModel K L₂)
    (φ : L₁ ≃+* L₂) (hφ : ∀ a : K, φ (algebraMap K L₁ a) = algebraMap K L₂ a)
    (θ : M₁.C ⟶ M₂.C) [IsIso θ] (hθ : θ ≫ M₂.toBase = M₁.toBase)

    (hθgen : M₁.C.fromSpecStalk (genericPoint M₁.C) ≫ θ =
      Spec.map (CommRingCat.ofHom
        (M₁.ffEquiv.toRingHom.comp (φ.symm.toRingHom.comp M₂.ffEquiv.symm.toRingHom))) ≫
        M₂.C.fromSpecStalk (genericPoint M₂.C))
    (x : {q : Spec (CommRingCat.of K) ⟶ M₁.C // q ≫ M₁.toBase = 𝟙 _}) :
    M₂.pointEquivPlace ⟨x.1 ≫ θ, by rw [Category.assoc, hθ, x.2]⟩ =
      Place.congrRingEquiv (e := φ) (he := hφ) (M₁.pointEquivPlace x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_pointEquivPlace_comp_eq_congrRingEquiv_of_fromSpecStalk_comp_eq.solution
