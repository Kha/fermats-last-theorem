import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CurveModel_exists_algEquiv_pointEquivPlace_comp_hom_eq_ofAlgAut_smul_pointEquivPlace

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u v

theorem AlgebraicCurve.CurveModel.exists_algEquiv_pointEquivPlace_comp_hom_eq_ofAlgAut_smul_pointEquivPlace
    (K : Type u) [Field K] [IsAlgClosed K] (L : Type v) [Field L] [Algebra K L]
    (M M' : AlgebraicCurve.CurveModel K L) (e : M.C ≅ M'.C) (he : e.hom ≫ M'.toBase = M.toBase) :
    ∃ τ : L ≃ₐ[K] L,
      ∀ x : {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _},
        M'.pointEquivPlace ⟨x.1 ≫ e.hom, by rw [Category.assoc, he]; exact x.2⟩ =
          SemilinearAut.ofAlgAut τ • M.pointEquivPlace x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_exists_algEquiv_pointEquivPlace_comp_hom_eq_ofAlgAut_smul_pointEquivPlace.solution
