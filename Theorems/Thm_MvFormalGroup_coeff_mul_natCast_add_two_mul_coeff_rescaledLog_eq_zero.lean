import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_coeff_mul_natCast_add_two_mul_coeff_rescaledLog_eq_zero

set_option autoImplicit false
open MvPowerSeries

universe u

theorem MvFormalGroup.coeff_mul_natCast_add_two_mul_coeff_rescaledLog_eq_zero
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {d : ℕ} (F : MvFormalGroup d 𝓞)
    (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1)
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
    (i j : Fin d) :
    (F.toPowerSeries i).coeff (Finsupp.single (Sum.inl j) 1 + Finsupp.single (Sum.inr j) 1) * (p : 𝓞) +
      2 * (φ i).coeff (Finsupp.single j 2) = 0 := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_coeff_mul_natCast_add_two_mul_coeff_rescaledLog_eq_zero.solution
