import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_HeckeOperatorForms
import P2M.Util
import P2M.Sol.S_CuspForm_exists_normalized_eigenvector
set_option autoImplicit false
open CuspForm ModularFormClass

theorem CuspForm.exists_normalized_eigenvector (N' : ℕ) [NeZero N'] (w : ℤ) (c : ℕ) (hc : 0 < c)
    (h : CuspForm (CongruenceSubgroup.Gamma0 N') w) (hh : h ≠ 0) (lam : ℕ → ℂ)
    (heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N'), ¬ ℓ ∣ c →
      heckeTLin w hℓ hℓN h = lam ℓ • h) :
    ∃ h' : CuspForm (CongruenceSubgroup.Gamma0 N') w,
      qCoeff h' 1 = 1 ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N'), ¬ ℓ ∣ c → heckeTLin w hℓ hℓN h' = lam ℓ • h') ∧
      (∀ n : ℕ, n.Coprime (c * N') →
        qCoeff h' n ∈ Algebra.adjoin ℤ {x : ℂ | ∃ ℓ : ℕ, ℓ.Prime ∧ ¬ ℓ ∣ c * N' ∧ x = lam ℓ}) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_normalized_eigenvector.solution
