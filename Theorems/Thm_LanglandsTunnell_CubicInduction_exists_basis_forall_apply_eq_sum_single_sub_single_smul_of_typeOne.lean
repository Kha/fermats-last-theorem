import Mathlib
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_basis_forall_apply_eq_sum_single_sub_single_smul_of_typeOne

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.exists_basis_forall_apply_eq_sum_single_sub_single_smul_of_typeOne
    (W : Type*) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Fin 3 → Fin 3 → (W →ₗ[ℂ] W))
    (hanti : ∀ (i j : Fin 3) (x : W), ρ j i x = -ρ i j x)
    (hrel₁ : ∀ x : W, ρ 0 1 (ρ 0 2 x) - ρ 0 2 (ρ 0 1 x) = -ρ 1 2 x)
    (hrel₂ : ∀ x : W, ρ 0 1 (ρ 1 2 x) - ρ 1 2 (ρ 0 1 x) = ρ 0 2 x)
    (hrel₃ : ∀ x : W, ρ 0 2 (ρ 1 2 x) - ρ 1 2 (ρ 0 2 x) = -ρ 0 1 x)
    (hcas : ∀ x : W, ρ 0 1 (ρ 0 1 x) + ρ 0 2 (ρ 0 2 x) + ρ 1 2 (ρ 1 2 x) = -((2 : ℂ) • x))
    (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ) (w₁ w₂ w' : W), B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w w' : W, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w : W, w ≠ 0 → 0 < (B w w).re)
    (hskew : ∀ (i j : Fin 3) (x y : W), B (ρ i j x) y = -B x (ρ i j y)) :
    ∃ (m : ℕ) (b : Module.Basis (Fin m × Fin 3) ℂ W), ∀ (i j : Fin 3) (t : Fin m) (c : Fin 3),
      ρ i j (b (t, c)) = ∑ d : Fin 3, ((Matrix.single i j (1 : ℂ) - Matrix.single j i 1 : Matrix (Fin 3) (Fin 3) ℂ) d c) • b (t, d) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_basis_forall_apply_eq_sum_single_sub_single_smul_of_typeOne.solution
