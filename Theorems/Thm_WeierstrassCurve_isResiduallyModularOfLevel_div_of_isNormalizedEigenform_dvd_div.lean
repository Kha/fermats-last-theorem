import Definitions.Def_FLTPrelim_ModularRep
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_isResiduallyModularOfLevel_div_of_isNormalizedEigenform_dvd_div
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

theorem WeierstrassCurve.isResiduallyModularOfLevel_div_of_isNormalizedEigenform_dvd_div {p L M N'' : ℕ} [Fact p.Prime] [NeZero M]
    {W : WeierstrassCurve ℤ}
    (hLM : L ∣ M) (hpL : p ^ 2 ∣ L) (hN'' : N'' ∣ M / p)
    (S₀ : Set ℕ)
    (hS₀rev : ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M / p → ℓ ≠ p → ℓ ∉ S₀)
    {f : CuspForm (CongruenceSubgroup.Gamma0 N'') 2} {𝔪' : Ideal (integralClosure ℤ ℂ)}
    (hf : f.IsNormalizedEigenform) (h𝔪' : 𝔪'.IsMaximal)
    (hp𝔪' : (p : integralClosure ℤ ℂ) ∈ 𝔪')
    (hcong : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N'' → ℓ ∉ S₀ →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
        a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪') :
    W.IsResiduallyModularOfLevel p (M / p) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_isResiduallyModularOfLevel_div_of_isNormalizedEigenform_dvd_div.solution
