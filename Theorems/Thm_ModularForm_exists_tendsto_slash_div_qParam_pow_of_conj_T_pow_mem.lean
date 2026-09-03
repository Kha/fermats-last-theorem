import Mathlib
import P2M.Util
import P2M.Sol.S_ModularForm_exists_tendsto_slash_div_qParam_pow_of_conj_T_pow_mem

set_option autoImplicit false

open UpperHalfPlane Filter Topology
open scoped MatrixGroups ModularForm

theorem ModularForm.exists_tendsto_slash_div_qParam_pow_of_conj_T_pow_mem
    (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k) (hf : f ≠ 0)
    (σ : SL(2, ℤ)) (h : ℕ) (hh : 0 < h) (hper : σ * ModularGroup.T ^ h * σ⁻¹ ∈ Γ) :
    ∃ (n : ℕ) (a : ℂ), a ≠ 0 ∧
      Tendsto (fun τ : ℍ => ((f : ℍ → ℂ) ∣[k] (σ : GL (Fin 2) ℝ)) τ / Function.Periodic.qParam h τ ^ n)
        atImInfty (𝓝 a) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_tendsto_slash_div_qParam_pow_of_conj_T_pow_mem.solution
