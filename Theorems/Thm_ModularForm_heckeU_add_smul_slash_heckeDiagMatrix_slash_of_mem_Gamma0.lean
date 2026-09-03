import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularForm_heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0

set_option autoImplicit false

open CongruenceSubgroup ModularForm
open scoped ModularForm UpperHalfPlane MatrixGroups

theorem ModularForm.heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0
    {N : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (ε : DirichletCharacter ℂ N)
    {f : ℍ → ℂ}
    (hf : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 N →
      f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ) = ε ((γ 1 1 : ℤ) : ZMod N) • f)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    (heckeU k p f + ε (p : ZMod N) • (f ∣[k] heckeDiagMatrix p)) ∣[k]
        (Matrix.SpecialLinearGroup.mapGL ℝ γ)
      = ε ((γ 1 1 : ℤ) : ZMod N) • (heckeU k p f + ε (p : ZMod N) • (f ∣[k] heckeDiagMatrix p)) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0.solution
