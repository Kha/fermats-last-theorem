import Mathlib
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_not_dvd_natCard_of_le_map_quaternion_units_of_prime_of_five_le

set_option autoImplicit false

open scoped MatrixGroups Quaternion

theorem CerednikDrinfeld.not_dvd_natCard_of_le_map_quaternion_units_of_prime_of_five_le
    (K₀ : Type) [Field K₀] [Algebra ℚ K₀]
    {a b : ℚ} (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀)
    (ρ : (ℍ[ℚ, a, b])ˣ →* PGL(2, K₀))
    (hρ : ∀ x : (ℍ[ℚ, a, b])ˣ, ρ x = Matrix.ProjGenLinGroup.mk
      (Units.map (ι : ℍ[ℚ, a, b] →* Matrix (Fin 2) (Fin 2) K₀) x)) :
    ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ H : Subgroup PGL(2, K₀),
      H ≤ (⊤ : Subgroup (ℍ[ℚ, a, b])ˣ).map ρ → Finite H → ¬ p ∣ Nat.card H := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_not_dvd_natCard_of_le_map_quaternion_units_of_prime_of_five_le.solution
