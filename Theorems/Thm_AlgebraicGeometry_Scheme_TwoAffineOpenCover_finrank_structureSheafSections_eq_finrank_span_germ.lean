import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_structureSheafSections_eq_finrank_span_germ

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_structureSheafSections_eq_finrank_span_germ
    (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) [IsIntegral C]
    (𝒱 : C.TwoAffineOpenCover) (h0 : genericPoint C ∈ 𝒱.U0) (h1 : genericPoint C ∈ 𝒱.U1) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    Module.finrank k (𝒱.structureSheafSections c).H0 =
        Module.finrank k ↥(Submodule.span k (Set.range (C.presheaf.germ (𝒱.U0) (genericPoint C) (h0)).hom) ⊓
          Submodule.span k (Set.range (C.presheaf.germ (𝒱.U1) (genericPoint C) (h1)).hom)) ∧
      Module.finrank k (𝒱.structureSheafSections c).H1 =
        Module.finrank k (↥(Submodule.span k (Set.range (C.presheaf.germ (𝒱.U0 ⊓ 𝒱.U1) (genericPoint C) (⟨h0, h1⟩)).hom)) ⧸
          (Submodule.span k (Set.range (C.presheaf.germ (𝒱.U0) (genericPoint C) (h0)).hom) ⊔ Submodule.span k (Set.range (C.presheaf.germ (𝒱.U1) (genericPoint C) (h1)).hom)).comap
            (Submodule.span k (Set.range (C.presheaf.germ (𝒱.U0 ⊓ 𝒱.U1) (genericPoint C) (⟨h0, h1⟩)).hom)).subtype) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_structureSheafSections_eq_finrank_span_germ.solution
