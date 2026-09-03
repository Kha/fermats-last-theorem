import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularForm_heckeU_slash_eq_self_of_mem_GammaH

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularForm.heckeU_slash_eq_self_of_mem_GammaH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) {q : ℕ} (hq : q.Prime) (hqM : q ∣ M)
    {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ))) :
    (ModularForm.heckeU k q f) ∣[k] γ = ModularForm.heckeU k q f := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_heckeU_slash_eq_self_of_mem_GammaH.solution
