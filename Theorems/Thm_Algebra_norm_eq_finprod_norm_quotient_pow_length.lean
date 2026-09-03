import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_norm_eq_finprod_norm_quotient_pow_length

set_option autoImplicit false

universe u v

theorem Algebra.norm_eq_finprod_norm_quotient_pow_length
    (K : Type u) [Field K] (A : Type v) [CommRing A] [Algebra K A] [Module.Finite K A] (a : A) :
    Algebra.norm K a =
      ∏ᶠ 𝔪 : MaximalSpectrum A,
        Algebra.norm K (Ideal.Quotient.mk 𝔪.asIdeal a) ^
          (Module.length (Localization.AtPrime 𝔪.asIdeal) (Localization.AtPrime 𝔪.asIdeal)).toNat := by p2m_exact_reverting @_root_.P2MW.S_Algebra_norm_eq_finprod_norm_quotient_pow_length.solution
