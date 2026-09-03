import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CurveModel_placeOfPoint_eq_smul_of_fromSpecStalk_comp_eq_frobenius

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u v

theorem AlgebraicCurve.CurveModel.placeOfPoint_eq_smul_of_fromSpecStalk_comp_eq_frobenius
    {K : Type u} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {L : Type v} [Field L] [Algebra K L] (M : CurveModel K L)
    (g : SemilinearAut K L)
    (Φ : L →ₐ[K] L) (hΦ : ∀ f : L, Φ f = (g⁻¹ • f) ^ p) (hfin : FiniteAlong K Φ)
    (θ : M.C ⟶ M.C)
    (hθgen : M.C.fromSpecStalk (genericPoint M.C) ≫ θ =
      Spec.map (CommRingCat.ofHom (M.ffEquiv.toRingHom.comp (Φ.toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫
        M.C.fromSpecStalk (genericPoint M.C))
    (y : closedPoints M.C) :
    ∃ h : θ.base y.1 ∈ closedPoints M.C, M.placeOfPoint ⟨θ.base y.1, h⟩ = g • M.placeOfPoint y := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_placeOfPoint_eq_smul_of_fromSpecStalk_comp_eq_frobenius.solution
