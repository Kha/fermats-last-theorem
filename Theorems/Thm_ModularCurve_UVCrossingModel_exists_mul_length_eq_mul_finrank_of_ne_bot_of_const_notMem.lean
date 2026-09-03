import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_mul_length_eq_mul_finrank_of_ne_bot_of_const_notMem

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

theorem ModularCurve.UVCrossingModel.exists_mul_length_eq_mul_finrank_of_ne_bot_of_const_notMem
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (P : PrimeSpectrum (UVCrossingModel W (ϖ ^ e))) (hP0 : P.asIdeal ≠ ⊥) (hPϖ : const (ϖ ^ e) ϖ ∉ P.asIdeal) :
    1 ≤ Module.finrank W (UVCrossingModel W (ϖ ^ e) ⧸ P.asIdeal) ∧
      Module.length W (UVCrossingModel W (ϖ ^ e) ⧸ (P.asIdeal ⊔ Ideal.span {U (ϖ ^ e)})) ≠ ⊤ ∧
      ∃ r : ℕ, 1 ≤ r ∧ ∃ p : ℕ, 1 ≤ p ∧ p + 1 ≤ r * e ∧
        (r : ℕ∞) * Module.length W (UVCrossingModel W (ϖ ^ e) ⧸ (P.asIdeal ⊔ Ideal.span {U (ϖ ^ e)})) =
          ((p * Module.finrank W (UVCrossingModel W (ϖ ^ e) ⧸ P.asIdeal) : ℕ) : ℕ∞) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_mul_length_eq_mul_finrank_of_ne_bot_of_const_notMem.solution
