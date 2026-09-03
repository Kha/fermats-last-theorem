import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_H1StructureSheaf_symm_eq_H1baseChangeMap_self

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_linearEquiv_H1StructureSheaf_symm_eq_H1baseChangeMap_self
    {R : Type u} [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (.of R)) :
    ∃ j : H1StructureSheaf c R 𝒱 ≃ₗ[R] (𝒱.structureSheafSections c).H1,
      ∀ y, j.symm y = Scheme.TwoAffineOpenCover.H1baseChangeMap 𝒱 c R y := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_H1StructureSheaf_symm_eq_H1baseChangeMap_self.solution
