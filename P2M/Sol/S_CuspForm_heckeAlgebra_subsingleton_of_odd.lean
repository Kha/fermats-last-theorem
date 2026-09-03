import Definitions.Def_CuspForm_HeckeAlgebra
import Theorems.Thm_CuspForm_eq_zero_of_odd_gamma0
import P2M.Util
namespace P2MW.S_CuspForm_heckeAlgebra_subsingleton_of_odd

set_option autoImplicit false

theorem solution (N : ℕ) [NeZero N] (k : ℤ) (hk : Odd k)
    (S : Set ℕ) : Subsingleton (CuspForm.heckeAlgebra N k S) := by
  refine ⟨fun a b => Subtype.ext (LinearMap.ext fun v => ?_)⟩
  rw [CuspForm.eq_zero_of_odd_gamma0 N k hk ((a : Module.End ℂ _) v),
    CuspForm.eq_zero_of_odd_gamma0 N k hk ((b : Module.End ℂ _) v)]
