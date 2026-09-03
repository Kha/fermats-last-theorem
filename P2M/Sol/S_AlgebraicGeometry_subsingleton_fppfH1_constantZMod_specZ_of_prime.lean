import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import Definitions.Def_AlgebraicGeometry_FppfAmitsurTrivial
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Theorems.Thm_AlgebraicGeometry_fppf_extClass_surjective
import Theorems.Thm_CategoryTheory_ShortComplex_ShortExact_extClass_eq_zero_iff_exists_section_g
import Theorems.Thm_AlgebraicGeometry_exists_section_of_fppfAmitsurTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_fppfAmitsurTrivial_constantZModSheaf
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_subsingleton_fppfH1_constantZMod_specZ_of_prime

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry"

theorem solution (p : ℕ) [Fact p.Prime] :
    Subsingleton (FppfCohomologyLES.FppfH
      (FppfKummerSES.sheafULift.{0}.obj
        (FppfRepresentableGroupSchemeSheaf.constantZModSheaf.{0} p)) 1) := by
  refine ⟨fun x y => ?_⟩
  suffices h : ∀ e : FppfCohomologyLES.FppfH (FppfKummerSES.sheafULift.{0}.obj
        (FppfRepresentableGroupSchemeSheaf.constantZModSheaf.{0} p)) 1, e = 0 by
    rw [h x, h y]
  intro e
  obtain ⟨E, f, g, w, hS, he⟩ := AlgebraicGeometry.fppf_extClass_surjective _ e
  rw [← he, hS.extClass_eq_zero_iff_exists_section_g]
  exact AlgebraicGeometry.exists_section_of_fppfAmitsurTrivial _ E f g w hS
    (fun A _ _ _ => AlgebraicGeometry.Scheme.fppfAmitsurTrivial_constantZModSheaf p
      (Fact.out : p.Prime).ne_zero A)
