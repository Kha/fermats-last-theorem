import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_mk_of_iso_of_forall_sigma_eq_smul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_mk_of_iso_of_forall_sigma_eq_smul
    {g N n : ℕ} {S : Type} [CommRing S] (X Y : FramedPolarisedAbelianScheme g N n S)
    (h : FramedPolarisedAbelianScheme.Iso X Y)
    (P : Scheme.Modules.ProjPresentation X.pol X.f N) (h₁ : IsClosedImmersion P.toProj)
    (h₂ : Scheme.Modules.IsSectionBasis X.f X.pol P.σ)
    (c : Γ(X.A, ⊤)) (hc : IsUnit c) (hσ : ∀ i : Fin (N + 1), P.σ i = c • X.frame.σ i) :
    FramedPolarisedAbelianScheme.Iso (⟨X.toPolarisedAbelianScheme, P, h₁, h₂⟩ : FramedPolarisedAbelianScheme g N n S) Y := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_mk_of_iso_of_forall_sigma_eq_smul.solution
