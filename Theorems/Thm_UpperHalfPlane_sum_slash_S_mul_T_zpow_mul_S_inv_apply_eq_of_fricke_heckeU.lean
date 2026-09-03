import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_UpperHalfPlane_sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_fricke_heckeU

set_option autoImplicit false

open scoped MatrixGroups ModularForm in

theorem UpperHalfPlane.sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_fricke_heckeU
    (N : ℕ) [NeZero N] (k : ℤ) {q : ℕ} (hq : q ≠ 0) (hqN : q ∣ N)
    (G H V : UpperHalfPlane → ℂ)
    (hGH : ∀ τ τ' : UpperHalfPlane, (τ' : ℂ) * ((N : ℂ) * (τ : ℂ)) = -1 →
      G τ' = (τ : ℂ) ^ k * H τ)
    (hUV : ∀ τ τ' : UpperHalfPlane, (τ' : ℂ) * ((N : ℂ) * (τ : ℂ)) = -1 →
      ModularForm.heckeU k q H τ' = (τ : ℂ) ^ k * V τ)
    (τ : UpperHalfPlane) :
    ∑ j ∈ Finset.range q,
        (G ∣[k] (ModularGroup.S * ModularGroup.T ^ ((j : ℤ) * (N / q : ℕ)) * ModularGroup.S⁻¹ :
          SL(2, ℤ))) τ
      = (q : ℂ) ^ (1 - k) * (-(N : ℂ)) ^ (-k) * V (ModularForm.heckeMatrix q 0 • τ) := by p2m_exact_reverting @_root_.P2MW.S_UpperHalfPlane_sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_fricke_heckeU.solution
