import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_surjectiveOnStalks_of_forall_exists_eq_sum_smul

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.surjectiveOnStalks_of_forall_exists_eq_sum_smul
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M : X.Modules} {N N' : ℕ}
    (𝔓 : M.ProjPresentation f N) (𝔔 : M.ProjPresentation f N') [SurjectiveOnStalks 𝔓.toProj]
    (h : ∀ i : Fin (N + 1), ∃ c : Fin (N' + 1) → R,
      𝔓.σ i = ∑ j, (f.appTop ((Scheme.ΓSpecIso (.of R)).inv (c j))) • 𝔔.σ j) :
    SurjectiveOnStalks 𝔔.toProj := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_surjectiveOnStalks_of_forall_exists_eq_sum_smul.solution
