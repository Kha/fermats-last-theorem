import Mathlib
import P2M.Util
import P2M.Sol.S_IsNoetherianRing_exists_faithfullyFlat_isAdicComplete_isAlgClosed_residueField_atPrime
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

theorem IsNoetherianRing.exists_faithfullyFlat_isAdicComplete_isAlgClosed_residueField_atPrime
    (S : Type) [CommRing S] [IsNoetherianRing S] (𝔭 : PrimeSpectrum S) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R) (_ : IsNoetherianRing R)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal R) R) (_ : IsAlgClosed (IsLocalRing.ResidueField R))
      (_ : Algebra S R) (_ : Algebra (Localization.AtPrime 𝔭.asIdeal) R)
      (_ : IsScalarTower S (Localization.AtPrime 𝔭.asIdeal) R),
      Module.FaithfullyFlat (Localization.AtPrime 𝔭.asIdeal) R := by p2m_exact_reverting @_root_.P2MW.S_IsNoetherianRing_exists_faithfullyFlat_isAdicComplete_isAlgClosed_residueField_atPrime.solution
