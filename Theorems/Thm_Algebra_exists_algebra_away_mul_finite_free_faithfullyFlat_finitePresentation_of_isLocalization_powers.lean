import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_algebra_away_mul_finite_free_faithfullyFlat_finitePresentation_of_isLocalization_powers

set_option autoImplicit false

theorem Algebra.exists_algebra_away_mul_finite_free_faithfullyFlat_finitePresentation_of_isLocalization_powers
    {S : Type} [CommRing S] (g r : S)
    (C : Type) [CommRing C] [Algebra S C] [Algebra (Localization.Away g) C] [IsScalarTower S (Localization.Away g) C]
    (hfin : Module.Finite (Localization.Away g) C) (hfree : Module.Free (Localization.Away g) C)
    (hff : Module.FaithfullyFlat (Localization.Away g) C) (hfp : Algebra.FinitePresentation (Localization.Away g) C)
    (C' : Type) [CommRing C'] [Algebra S C'] [Algebra C C'] [IsScalarTower S C C']
    [IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers r)) C'] :
    ∃ (_ : Algebra (Localization.Away (g * r)) C') (_ : IsScalarTower S (Localization.Away (g * r)) C'),
      Module.Finite (Localization.Away (g * r)) C' ∧ Module.Free (Localization.Away (g * r)) C' ∧
      Module.FaithfullyFlat (Localization.Away (g * r)) C' ∧ Algebra.FinitePresentation (Localization.Away (g * r)) C' := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_algebra_away_mul_finite_free_faithfullyFlat_finitePresentation_of_isLocalization_powers.solution
