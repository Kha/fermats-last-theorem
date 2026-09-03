import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_iso_nonempty_pullback_pol_iso_of_isPullback_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_iso_nonempty_pullback_pol_iso_of_isPullback_of_isPullback
    {g d n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : PolarisedAbelianScheme g d n S) (v v' : PolarisedAbelianScheme g d n S')
    (h : PolarisedAbelianScheme.IsPullback φ u v) (h' : PolarisedAbelianScheme.IsPullback φ u v') :
    ∃ (e : v.A ≅ v'.A) (he : e.hom ≫ v'.f = v.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t v.f),
        (v.L.mul t x y).1 ≫ e.hom =
          (v'.L.mul t ⟨x.1 ≫ e.hom, by rw [Category.assoc, he]; exact x.2⟩
            ⟨y.1 ≫ e.hom, by rw [Category.assoc, he]; exact y.2⟩).1) ∧
      (∀ i, (v.P i).1 ≫ e.hom = (v'.P i).1) ∧
      Nonempty ((Scheme.Modules.pullback e.hom).obj v'.pol ≅ v.pol) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_iso_nonempty_pullback_pol_iso_of_isPullback_of_isPullback.solution
