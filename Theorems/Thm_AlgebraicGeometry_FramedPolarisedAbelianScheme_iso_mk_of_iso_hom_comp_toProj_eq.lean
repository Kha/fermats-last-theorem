import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_mk_of_iso_hom_comp_toProj_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_mk_of_iso_hom_comp_toProj_eq
    {g N n : ℕ} {S : Type} [CommRing S] (u : PolarisedAbelianScheme g (N + 1) n S)
    (X' : FramedPolarisedAbelianScheme g N n S)
    (e : u.A ≅ X'.A) (he : e.hom ≫ X'.f = u.f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t u.f),
      (u.L.mul t x y).1 ≫ e.hom =
        (X'.L.mul t ⟨x.1 ≫ e.hom, by rw [Category.assoc, he]; exact x.2⟩
          ⟨y.1 ≫ e.hom, by rw [Category.assoc, he]; exact y.2⟩).1)
    (hP : ∀ i, (u.P i).1 ≫ e.hom = (X'.P i).1)
    (ψ : (Scheme.Modules.pullback e.hom).obj X'.pol ≅ u.pol)
    (P : Scheme.Modules.ProjPresentation u.pol u.f N) (h₁ : IsClosedImmersion P.toProj)
    (h₂ : Scheme.Modules.IsSectionBasis u.f u.pol P.σ) (hto : P.toProj = e.hom ≫ X'.frame.toProj) :
    FramedPolarisedAbelianScheme.Iso (⟨u, P, h₁, h₂⟩ : FramedPolarisedAbelianScheme g N n S) X' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_mk_of_iso_hom_comp_toProj_eq.solution
