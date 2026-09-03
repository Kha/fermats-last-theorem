import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_PolarisedAbelianScheme_isPullback_refl_comp_cancel_iso_symm_trans

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.PolarisedAbelianScheme

universe u

theorem AlgebraicGeometry.PolarisedAbelianScheme.isPullback_refl_comp_cancel_iso_symm_trans (g d n : ℕ) :
    (∀ (S : Type u) [CommRing S] (u : PolarisedAbelianScheme g d n S),
        PolarisedAbelianScheme.IsPullback (RingHom.id S) u u) ∧
    (∀ (S S' S'' : Type u) [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'')
        (u : PolarisedAbelianScheme g d n S) (u' : PolarisedAbelianScheme g d n S')
        (u'' : PolarisedAbelianScheme g d n S''),
        PolarisedAbelianScheme.IsPullback φ u u' → PolarisedAbelianScheme.IsPullback ψ u' u'' →
          PolarisedAbelianScheme.IsPullback (ψ.comp φ) u u'') ∧
    (∀ (S S' S'' : Type u) [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'')
        (u : PolarisedAbelianScheme g d n S) (u' : PolarisedAbelianScheme g d n S')
        (u'' : PolarisedAbelianScheme g d n S''),
        PolarisedAbelianScheme.IsPullback φ u u' → PolarisedAbelianScheme.IsPullback (ψ.comp φ) u u'' →
          PolarisedAbelianScheme.IsPullback ψ u' u'') ∧
    (∀ (S S' : Type u) [CommRing S] [CommRing S'] (φ : S →+* S')
        (u : PolarisedAbelianScheme g d n S) (u'₁ u'₂ : PolarisedAbelianScheme g d n S'),
        PolarisedAbelianScheme.IsPullback φ u u'₁ → PolarisedAbelianScheme.IsPullback φ u u'₂ →
          PolarisedAbelianScheme.IsPullback (RingHom.id S') u'₁ u'₂) ∧
    (∀ (S : Type u) [CommRing S] (u u' : PolarisedAbelianScheme g d n S),
        PolarisedAbelianScheme.IsPullback (RingHom.id S) u u' → PolarisedAbelianScheme.Iso u u') ∧
    (∀ (S : Type u) [CommRing S] (u : PolarisedAbelianScheme g d n S), PolarisedAbelianScheme.Iso u u) ∧
    (∀ (S : Type u) [CommRing S] (u u' : PolarisedAbelianScheme g d n S),
        PolarisedAbelianScheme.Iso u u' → PolarisedAbelianScheme.Iso u' u) ∧
    (∀ (S : Type u) [CommRing S] (u u' u'' : PolarisedAbelianScheme g d n S),
        PolarisedAbelianScheme.Iso u u' → PolarisedAbelianScheme.Iso u' u'' → PolarisedAbelianScheme.Iso u u'') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_isPullback_refl_comp_cancel_iso_symm_trans.solution
