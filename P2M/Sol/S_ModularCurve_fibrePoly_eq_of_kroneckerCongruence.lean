import Definitions.Def_ModularCurve_FibrePoly
import P2M.Util
namespace P2MW.S_ModularCurve_fibrePoly_eq_of_kroneckerCongruence
open Polynomial ModularCurve
theorem solution {k : Type*} [Field k]
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ] (data : ModularCurve.ModularPolynomialData ℓ)
    (hK : ModularCurve.KroneckerCongruence ℓ data) (a : k) :
    ModularCurve.fibrePoly data.Φ a =
      (Polynomial.C (a ^ ℓ) - Polynomial.X) * (Polynomial.C a - Polynomial.X ^ ℓ) := by
  have hK' : reduceModBivar ℓ data.Φ =
      (Polynomial.C Polynomial.X ^ ℓ - Polynomial.X) *
        (Polynomial.C Polynomial.X - Polynomial.X ^ ℓ) := hK
  rw [fibrePoly_eq_map_reduceModBivar (ℓ := ℓ), hK']
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, map_pow]
