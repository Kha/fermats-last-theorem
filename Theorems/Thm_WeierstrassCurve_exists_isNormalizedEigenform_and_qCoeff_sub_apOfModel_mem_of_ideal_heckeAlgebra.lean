import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_HeckeAlgebra
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_isNormalizedEigenform_and_qCoeff_sub_apOfModel_mem_of_ideal_heckeAlgebra
attribute [-simp] PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU

set_option autoImplicit false

open CuspForm

theorem WeierstrassCurve.exists_isNormalizedEigenform_and_qCoeff_sub_apOfModel_mem_of_ideal_heckeAlgebra (W : WeierstrassCurve ℤ) (p : ℕ) (N : ℕ) [NeZero N] (S : Set ℕ)
    (𝔪 : Ideal (heckeAlgebra N 2 S)) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : heckeAlgebra N 2 S) ∈ 𝔪)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
      heckeAlgebra.T hℓ hℓN hℓS - (W.apOfModel ℓ : heckeAlgebra N 2 S) ∈ 𝔪) :
    ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (𝔪' : Ideal (integralClosure ℤ ℂ)),
      f.IsNormalizedEigenform ∧ 𝔪'.IsMaximal ∧ (p : integralClosure ℤ ℂ) ∈ 𝔪' ∧
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S →
        ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
          a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪' := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_isNormalizedEigenform_and_qCoeff_sub_apOfModel_mem_of_ideal_heckeAlgebra.solution
