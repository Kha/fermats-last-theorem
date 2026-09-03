import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDifferentialsModL
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_conj_mem_GammaH_div

set_option autoImplicit false

open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.exists_conj_mem_GammaH_div
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CohCarrier.GammaH M H) :
    ∃ γ₁ ∈ CohCarrier.GammaH (M / p) (infSubgroup p M H hpM),
      γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (p : ℤ) * γ 0 1 ∧ (p : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_conj_mem_GammaH_div.solution
