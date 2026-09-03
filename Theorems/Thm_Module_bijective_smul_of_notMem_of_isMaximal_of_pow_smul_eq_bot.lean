import Mathlib
import P2M.Util
import P2M.Sol.S_Module_bijective_smul_of_notMem_of_isMaximal_of_pow_smul_eq_bot

theorem Module.bijective_smul_of_notMem_of_isMaximal_of_pow_smul_eq_bot
    {T : Type*} [CommRing T] {M : Type*} [AddCommGroup M] [Module T M]
    (𝔓 : Ideal T) (h𝔓 : 𝔓.IsMaximal) (k : ℕ) (hk : ∀ (a : T), a ∈ 𝔓 ^ k → ∀ x : M, a • x = 0)
    (u : T) (hu : u ∉ 𝔓) : Function.Bijective (fun x : M => u • x) := by p2m_exact_reverting @_root_.P2MW.S_Module_bijective_smul_of_notMem_of_isMaximal_of_pow_smul_eq_bot.solution
