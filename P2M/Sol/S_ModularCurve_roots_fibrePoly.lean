import Definitions.Def_ModularCurve_FibrePoly
import P2M.Util
namespace P2MW.S_ModularCurve_roots_fibrePoly
open Polynomial ModularCurve
theorem solution {k : Type*} [Field k] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP k ℓ] [PerfectRing k ℓ] (data : ModularCurve.ModularPolynomialData ℓ)
    (hK : ModularCurve.KroneckerCongruence ℓ data) (a : k) :
    (ModularCurve.fibrePoly data.Φ a).roots =
      {a ^ ℓ} + ℓ • {(frobeniusEquiv k ℓ).symm a} := by
  have h1 : fibrePoly data.Φ a =
      (Polynomial.C (a ^ ℓ) - Polynomial.X) * (Polynomial.C a - Polynomial.X ^ ℓ) := by
    have hK' : reduceModBivar ℓ data.Φ =
        (Polynomial.C Polynomial.X ^ ℓ - Polynomial.X) *
          (Polynomial.C Polynomial.X - Polynomial.X ^ ℓ) := hK
    rw [fibrePoly_eq_map_reduceModBivar (ℓ := ℓ), hK']
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, map_pow]
  have hfact : fibrePoly data.Φ a =
      (Polynomial.X - Polynomial.C (a ^ ℓ)) *
        (Polynomial.X - Polynomial.C ((frobeniusEquiv k ℓ).symm a)) ^ ℓ := by
    rw [h1, C_sub_X_pow_eq_neg_pow, ← neg_sub Polynomial.X (Polynomial.C (a ^ ℓ)), neg_mul_neg]
  rw [hfact,
    Polynomial.roots_mul (((Polynomial.monic_X_sub_C (a ^ ℓ)).mul
      ((Polynomial.monic_X_sub_C ((frobeniusEquiv k ℓ).symm a)).pow ℓ)).ne_zero),
    Polynomial.roots_pow, Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
