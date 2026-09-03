import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CurveModel_exists_semilinearAut_baseAut_eq_and_pointEquivPlace_eq_smul

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicCurve.CurveModel.exists_semilinearAut_baseAut_eq_and_pointEquivPlace_eq_smul
    {K : Type u} [Field K] [IsAlgClosed K] {L : Type v} [Field L] [Algebra K L]
    (M : AlgebraicCurve.CurveModel K L) (τ : K ≃+* K) (h : M.C ⟶ M.C) [IsIso h]
    (hh : h ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom (τ : K →+* K))) :
    ∃ g : AlgebraicCurve.SemilinearAut K L,
      AlgebraicCurve.SemilinearAut.baseAut g = τ ∧
      (∀ (U : M.C.Opens) [Nonempty (Scheme.Opens.toScheme U)] [Nonempty (Scheme.Opens.toScheme (h ⁻¹ᵁ U))]
        (t : Γ(M.C, U)),
        g • M.ffEquiv.symm (M.C.germToFunctionField U t) =
          M.ffEquiv.symm (M.C.germToFunctionField (h ⁻¹ᵁ U) ((h.app U).hom t))) ∧
      ∀ x y : {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _},
        y.1 ≫ h = Spec.map (CommRingCat.ofHom (τ : K →+* K)) ≫ x.1 →
          M.pointEquivPlace y = g • M.pointEquivPlace x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_exists_semilinearAut_baseAut_eq_and_pointEquivPlace_eq_smul.solution
