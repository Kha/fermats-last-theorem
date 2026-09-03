import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_HeckeAlgebra
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_ideal_heckeAlgebra_ordCompl_of_isNewform_sq_dvd
attribute [-simp] ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU CuspForm.coe_heckeULowerLin_apply

set_option autoImplicit false

open CuspForm

theorem WeierstrassCurve.exists_ideal_heckeAlgebra_ordCompl_of_isNewform_sq_dvd (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ)
    (hΔ : W.Δ ≠ 0) (hirr : W.ModRepIsIrreducible p)
    {L : ℕ} [NeZero L] (hpL : p ^ 2 ∣ L)
    (S₀ : Set ℕ) (hS₀fin : S₀.Finite) (hS₀p : p ∈ S₀)
    (hS₀L : ∀ q : ℕ, q.Prime → q ∣ L → q ∈ S₀)
    (hS₀Δ : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ W.Δ → q ∈ S₀)
    (g : CuspForm (CongruenceSubgroup.Gamma0 L) 2) (𝔪 : Ideal (integralClosure ℤ ℂ))
    (hg : g.IsNewform) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    (hcong : ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ℓ ∉ S₀ →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff g ℓ ∧
        a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪)
    (N' : ℕ) [NeZero N'] (hN' : N' = L / p ^ (L.factorization p)) :
    ∃ k : ℤ, 2 ≤ k ∧
      ∃ 𝔪ₖ : Ideal (heckeAlgebra N' k S₀), 𝔪ₖ.IsMaximal ∧
        (p : heckeAlgebra N' k S₀) ∈ 𝔪ₖ ∧
        ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ N'),
          W.IsGoodPrimeFor ℓ →
            heckeAlgebra.T hℓ hℓN hℓS -
              ((W.apOfModel ℓ : ℤ) : heckeAlgebra N' k S₀) ∈ 𝔪ₖ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_ideal_heckeAlgebra_ordCompl_of_isNewform_sq_dvd.solution
