import Mathlib
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_exists_rational_clearedFE_finset_sum

set_option autoImplicit false

theorem LanglandsTunnell.TateLocal.exists_rational_clearedFE_finset_sum
    (q : ℂ) (hq : q ≠ 0) (Γn Γd : Polynomial ℂ) (eΓ : ℤ)
    {ι : Type*} (S : Finset ι) (c : ι → ℂ) (Z Zd : ι → ℂ → ℂ)
    (P Pd Q Qd : ι → Polynomial ℂ) (m md : ι → ℤ) (σ σd : ι → ℝ)
    (hQ : ∀ i ∈ S, Q i ≠ 0) (hQd : ∀ i ∈ S, Qd i ≠ 0)
    (h1 : ∀ i ∈ S, ∀ s : ℂ, σ i < s.re →
      Z i s * (Q i).eval (q ^ (-s)) = q ^ ((m i : ℂ) * s) * (P i).eval (q ^ (-s)))
    (h2 : ∀ i ∈ S, ∀ s : ℂ, σd i < s.re →
      Zd i s * (Qd i).eval (q ^ (-s)) = q ^ ((md i : ℂ) * s) * (Pd i).eval (q ^ (-s)))
    (h3 : ∀ i ∈ S, ∀ s : ℂ,
      q ^ ((md i : ℂ) * s) * (Pd i).eval (q ^ (-s)) * (Q i).eval (q ^ s) * Γd.eval (q ^ (-s)) =
        Γn.eval (q ^ (-s)) * q ^ ((eΓ : ℂ) * s) * (q ^ ((m i : ℂ) * (-s)) * (P i).eval (q ^ s)) * (Qd i).eval (q ^ (-s))) :
    ∃ (P' Pd' Q' Qd' : Polynomial ℂ) (m' md' : ℤ) (σ' σd' : ℝ), Q' ≠ 0 ∧ Qd' ≠ 0 ∧
      (∀ i ∈ S, σ i ≤ σ' ∧ σd i ≤ σd') ∧
      (∀ s : ℂ, σ' < s.re →
        (∑ i ∈ S, c i * Z i s) * Q'.eval (q ^ (-s)) = q ^ ((m' : ℂ) * s) * P'.eval (q ^ (-s))) ∧
      (∀ s : ℂ, σd' < s.re →
        (∑ i ∈ S, c i * Zd i s) * Qd'.eval (q ^ (-s)) = q ^ ((md' : ℂ) * s) * Pd'.eval (q ^ (-s))) ∧
      (∀ s : ℂ,
        q ^ ((md' : ℂ) * s) * Pd'.eval (q ^ (-s)) * Q'.eval (q ^ s) * Γd.eval (q ^ (-s)) =
          Γn.eval (q ^ (-s)) * q ^ ((eΓ : ℂ) * s) * (q ^ ((m' : ℂ) * (-s)) * P'.eval (q ^ s)) * Qd'.eval (q ^ (-s))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_exists_rational_clearedFE_finset_sum.solution
