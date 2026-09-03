import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_sigma_eq_app_unit_and_toProj_eq_comp_of_iso
attribute [-simp] AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_sigma_eq_app_unit_and_toProj_eq_comp_of_iso
    {S : Type u} [CommRing S] {N : ℕ} {A A' : Scheme.{u}} (e : A ≅ A')
    {f : A ⟶ Spec (.of S)} {f' : A' ⟶ Spec (.of S)} (he : e.hom ≫ f' = f)
    {M : A.Modules} {M' : A'.Modules} (ψ : (Scheme.Modules.pullback e.hom).obj M' ≅ M)
    (P' : M'.ProjPresentation f' N) (h₁ : IsClosedImmersion P'.toProj)
    (h₂ : Scheme.Modules.IsSectionBasis f' M' P'.σ) :
    ∃ P : M.ProjPresentation f N,
      (∀ i : Fin (N + 1), P.σ i =
        ψ.hom.app ⊤ ((((Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit.app M').app ⊤) (P'.σ i))) ∧
      P.toProj = e.hom ≫ P'.toProj ∧ IsClosedImmersion P.toProj ∧ Scheme.Modules.IsSectionBasis f M P.σ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_sigma_eq_app_unit_and_toProj_eq_comp_of_iso.solution
