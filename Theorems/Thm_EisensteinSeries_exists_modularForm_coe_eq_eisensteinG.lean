import Mathlib
import Definitions.Def_EisensteinSeries_EisensteinG
import P2M.Util
import P2M.Sol.S_EisensteinSeries_exists_modularForm_coe_eq_eisensteinG

set_option autoImplicit false

open Matrix
open scoped MatrixGroups CongruenceSubgroup ModularForm

theorem EisensteinSeries.exists_modularForm_coe_eq_eisensteinG
    (N : ℕ) [NeZero N] (k : ℤ) (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    (∃ F : ModularForm Γ(N) k, ⇑F = EisensteinSeries.eisensteinG N k a) ∧
      ∀ γ : SL(2, ℤ), EisensteinSeries.eisensteinG N k a ∣[k] γ =
        EisensteinSeries.eisensteinG N k (a ᵥ* γ) := by p2m_exact_reverting @_root_.P2MW.S_EisensteinSeries_exists_modularForm_coe_eq_eisensteinG.solution
