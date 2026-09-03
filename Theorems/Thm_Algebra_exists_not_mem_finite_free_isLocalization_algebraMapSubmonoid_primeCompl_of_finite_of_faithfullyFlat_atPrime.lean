import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import P2M.Util
import P2M.Sol.S_Algebra_exists_not_mem_finite_free_isLocalization_algebraMapSubmonoid_primeCompl_of_finite_of_faithfullyFlat_atPrime

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem Algebra.exists_not_mem_finite_free_isLocalization_algebraMapSubmonoid_primeCompl_of_finite_of_faithfullyFlat_atPrime
    {S : Type} [CommRing S] [IsNoetherianRing S] (𝔭 : PrimeSpectrum S)
    (C₀ : Type) [CommRing C₀] [Algebra S C₀] [Algebra (Localization.AtPrime 𝔭.asIdeal) C₀]
    [IsScalarTower S (Localization.AtPrime 𝔭.asIdeal) C₀]
    (hfin : Module.Finite (Localization.AtPrime 𝔭.asIdeal) C₀) (hff : Module.FaithfullyFlat (Localization.AtPrime 𝔭.asIdeal) C₀) :
    ∃ (g : S) (_ : g ∉ 𝔭.asIdeal) (C : Type) (_ : CommRing C) (_ : Algebra S C) (_ : Algebra (Localization.Away g) C)
      (_ : IsScalarTower S (Localization.Away g) C) (_ : Algebra C C₀) (_ : IsScalarTower S C C₀),
      Module.Finite (Localization.Away g) C ∧ Module.Free (Localization.Away g) C ∧
      Module.FaithfullyFlat (Localization.Away g) C ∧ Algebra.FinitePresentation (Localization.Away g) C ∧
      IsLocalization (Algebra.algebraMapSubmonoid C 𝔭.asIdeal.primeCompl) C₀ := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_not_mem_finite_free_isLocalization_algebraMapSubmonoid_primeCompl_of_finite_of_faithfullyFlat_atPrime.solution
