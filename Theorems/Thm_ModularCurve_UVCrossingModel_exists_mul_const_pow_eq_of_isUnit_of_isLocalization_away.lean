import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_mul_const_pow_eq_of_isUnit_of_isLocalization_away
set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel

theorem ModularCurve.UVCrossingModel.exists_mul_const_pow_eq_of_isUnit_of_isLocalization_away
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    {S : Type*} [CommRing S] [Algebra (UVCrossingModel W (ϖ ^ e)) S]
    [IsLocalization.Away (const (ϖ ^ e) ϖ) S] (g : S) (hg : IsUnit g) :
    ∃ (w : (UVCrossingModel W (ϖ ^ e))ˣ) (a b n k : ℕ), (a = 0 ∨ b = 0) ∧
      g * algebraMap (UVCrossingModel W (ϖ ^ e)) S (const (ϖ ^ e) ϖ) ^ k =
        algebraMap (UVCrossingModel W (ϖ ^ e)) S
          (w * U (ϖ ^ e) ^ a * V (ϖ ^ e) ^ b * const (ϖ ^ e) ϖ ^ n) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_mul_const_pow_eq_of_isUnit_of_isLocalization_away.solution
