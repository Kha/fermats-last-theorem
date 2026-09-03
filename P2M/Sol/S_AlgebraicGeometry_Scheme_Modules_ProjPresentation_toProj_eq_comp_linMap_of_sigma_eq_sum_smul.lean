import Definitions.Def_AlgebraicGeometry_ProjSpaceLinMap
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_sigma_eq_sum_smul_toProj_eq_comp_linMap
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_of_forall_sections_eq_univ
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_comp_linMap_of_sigma_eq_sum_smul

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M : X.Modules} {N : ℕ}
    (𝔓 𝔔 : M.ProjPresentation f N) (U : Matrix (Fin (N + 1)) (Fin (N + 1)) R) (hU : IsUnit U)
    (h : ∀ i, 𝔔.σ i = ∑ j, ((f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (.of R)).inv.hom (U i j))) • 𝔓.σ j) :
    𝔔.toProj = 𝔓.toProj ≫ ProjSpace.linMap R N U hU  := by
  obtain ⟨𝔓', hσ, hto⟩ :=
    AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_sigma_eq_sum_smul_toProj_eq_comp_linMap 𝔓 U hU
  have h𝔔 : 𝔔.toProj = 𝔓'.toProj :=
    AlgebraicGeometry.Scheme.Modules.ProjPresentation.toProj_eq_of_forall_sections_eq_univ 𝔔 𝔓'
      (fun i => by rw [h i, hσ i])
  rw [h𝔔, hto]
