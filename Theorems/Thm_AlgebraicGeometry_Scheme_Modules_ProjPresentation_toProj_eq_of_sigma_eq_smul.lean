import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_of_sigma_eq_smul

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.toProj_eq_of_sigma_eq_smul
    {R : Type u} [CommRing R] {X : Scheme.{u}} {M : X.Modules} {f : X ⟶ Spec (CommRingCat.of R)} {N : ℕ}
    (P P' : M.ProjPresentation f N) (c : Γ(X, ⊤)) (hc : IsUnit c)
    (h : ∀ i : Fin (N + 1), P'.σ i = c • P.σ i) :
    P'.toProj = P.toProj := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_of_sigma_eq_smul.solution
