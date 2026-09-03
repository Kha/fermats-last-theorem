import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_PolarisedAbelianScheme_IsPullback_nonempty_pullback_one_pol_iso_unit_of_pullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.nonempty_pullback_one_pol_iso_unit_of_pullback
    {g d n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : PolarisedAbelianScheme g d n S) (v : PolarisedAbelianScheme g d n S')
    (h : PolarisedAbelianScheme.IsPullback φ u v)

    (hu : Nonempty ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).obj
      ((Scheme.Modules.pullback (u.L.one (𝟙 _)).1).obj u.pol) ≅ SheafOfModules.unit (Spec (CommRingCat.of S')).ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback (v.L.one (𝟙 _)).1).obj v.pol ≅ SheafOfModules.unit (Spec (CommRingCat.of S')).ringCatSheaf) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_IsPullback_nonempty_pullback_one_pol_iso_unit_of_pullback.solution
