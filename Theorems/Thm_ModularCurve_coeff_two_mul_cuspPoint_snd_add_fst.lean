import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import P2M.Util
import P2M.Sol.S_ModularCurve_coeff_two_mul_cuspPoint_snd_add_fst

set_option autoImplicit false

theorem ModularCurve.coeff_two_mul_cuspPoint_snd_add_fst
    (L : Type) [Field L] (N : ℕ) [NeZero N] (ξ : Lˣ) (hξ : IsPrimitiveRoot (ξ : L) N)
    (v : Fin 2 → ZMod N) (hv : v ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    (2 * (ModularCurve.cuspPoint L N ξ v).2 + (ModularCurve.cuspPoint L N ξ v).1).coeff (n : ℤ) =
      ∑ md ∈ Nat.divisorsAntidiagonal n,
        ((md.2 : ℕ) : L) ^ 2 *
          ((if ((md.1 : ℕ) : ZMod N) = v 1 then ((ξ ^ (md.2 * (v 0).val) : Lˣ) : L) else 0) -
            (if ((md.1 : ℕ) : ZMod N) = -v 1 then ((ξ⁻¹ ^ (md.2 * (v 0).val) : Lˣ) : L) else 0)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeff_two_mul_cuspPoint_snd_add_fst.solution
