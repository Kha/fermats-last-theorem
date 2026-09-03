import Definitions.Def_AlgebraicGeometry_ProjSpaceLinMap
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_sigma_eq_sum_smul_toProj_eq_comp_linMap

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_sigma_eq_sum_smul_toProj_eq_comp_linMap
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M : X.Modules} {N : ℕ}
    (𝔓 : M.ProjPresentation f N) (U : Matrix (Fin (N + 1)) (Fin (N + 1)) R) (hU : IsUnit U) :
    ∃ 𝔓' : M.ProjPresentation f N,
      (∀ i, 𝔓'.σ i = ∑ j, ((f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (.of R)).inv.hom (U i j))) • 𝔓.σ j) ∧
      𝔓'.toProj = 𝔓.toProj ≫ ProjSpace.linMap R N U hU := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_sigma_eq_sum_smul_toProj_eq_comp_linMap.solution
