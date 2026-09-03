import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_prime_V_sub_const_pow_mem

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

theorem ModularCurve.UVCrossingModel.exists_prime_V_sub_const_pow_mem
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (d : ℕ) (hd1 : 1 ≤ d) (hde : d + 1 ≤ e) :
    ∃ Q : PrimeSpectrum (UVCrossingModel W (ϖ ^ e)),
      Q.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ Q.asIdeal ∧ V (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ d) ∈ Q.asIdeal ∧
      U (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ (e - d)) ∈ Q.asIdeal ∧
      (∀ P : PrimeSpectrum (UVCrossingModel W (ϖ ^ e)), const (ϖ ^ e) ϖ ∉ P.asIdeal →
        V (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ d) ∈ P.asIdeal → P = Q) ∧
      Module.Free W (UVCrossingModel W (ϖ ^ e) ⧸ Q.asIdeal) ∧ Module.Finite W (UVCrossingModel W (ϖ ^ e) ⧸ Q.asIdeal) ∧
      Module.finrank W (UVCrossingModel W (ϖ ^ e) ⧸ Q.asIdeal) = 1 ∧
      Algebra.norm W (Ideal.Quotient.mk Q.asIdeal (V (ϖ ^ e))) = ϖ ^ d ∧
      Module.length (Localization.AtPrime Q.asIdeal)
        (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {V (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ d)})) = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_prime_V_sub_const_pow_mem.solution
