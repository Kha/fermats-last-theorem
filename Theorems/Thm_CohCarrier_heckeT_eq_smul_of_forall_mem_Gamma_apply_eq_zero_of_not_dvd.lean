import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_heckeT_eq_smul_of_forall_mem_Gamma_apply_eq_zero_of_not_dvd

set_option autoImplicit false

open scoped MatrixGroups

theorem CohCarrier.heckeT_eq_smul_of_forall_mem_Gamma_apply_eq_zero_of_not_dvd
    (N : ℕ) (A : Type*) [AddCommGroup A] (φ : CohCarrier.H1 N ⊤ A)
    (M : ℕ) (hM : 0 < M) (hφ : ∀ γ : ↥(CohCarrier.GammaH N ⊤),
      (γ : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma M → φ (Additive.ofMul γ) = 0)
    (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓM : ¬ ℓ ∣ M) :
    CohCarrier.heckeT N ⊤ ℓ A φ = (ℓ + 1) • φ := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_heckeT_eq_smul_of_forall_mem_Gamma_apply_eq_zero_of_not_dvd.solution
