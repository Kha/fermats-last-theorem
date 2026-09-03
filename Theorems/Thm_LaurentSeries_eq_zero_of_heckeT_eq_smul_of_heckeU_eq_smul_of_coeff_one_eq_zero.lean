import Mathlib
import Definitions.Def_LaurentSeries_HeckeU
import Definitions.Def_LaurentSeries_HeckeV
import P2M.Util
import P2M.Sol.S_LaurentSeries_eq_zero_of_heckeT_eq_smul_of_heckeU_eq_smul_of_coeff_one_eq_zero

set_option autoImplicit false

theorem LaurentSeries.eq_zero_of_heckeT_eq_smul_of_heckeU_eq_smul_of_coeff_one_eq_zero
    (R : Type*) [CommRing R] (M k : ℕ) (θ : Nat.Primes → R) (f : LaurentSeries R)
    (hneg : ∀ n : ℤ, n ≤ 0 → f.coeff n = 0)
    (hT : ∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ M → LaurentSeries.heckeT R (ℓ : ℕ) ℓ.2.pos k f = θ ℓ • f)
    (hU : ∀ q : Nat.Primes, (q : ℕ) ∣ M → LaurentSeries.heckeU R (q : ℕ) q.2.pos f = θ q • f)
    (h1 : f.coeff 1 = 0) :
    f = 0 := by p2m_exact_reverting @_root_.P2MW.S_LaurentSeries_eq_zero_of_heckeT_eq_smul_of_heckeU_eq_smul_of_coeff_one_eq_zero.solution
