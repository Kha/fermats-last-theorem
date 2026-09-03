import Definitions.Def_CuspForm_Newforms
import P2M.Util
import P2M.Sol.S_CuspForm_exists_isNewform_descent
open scoped CongruenceSubgroup
open CongruenceSubgroup ModularFormClass in
theorem CuspForm.exists_isNewform_descent {N : ℕ} [NeZero N]
    (f : CuspForm (Gamma0 N) 2) (hf : f.IsNormalizedEigenform) :
    ∃ (M : ℕ) (_ : M ∣ N) (g : CuspForm (Gamma0 M) 2),
      g.IsNewform ∧ ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → qCoeff g ℓ = qCoeff f ℓ := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_isNewform_descent.solution
