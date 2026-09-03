import Definitions.Def_ModularCurve_EichlerShimuraData
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.LinearAlgebra.FreeModule.PID
import P2M.Util
import P2M.Sol.S_W54_finite_free_tateModule

open ModularCurve
theorem W54.finite_free_tateModule {J : Type} [AddCommGroup J] [Module HeckeAlg J] {p : ℕ} [Fact p.Prime] [Module ℤ_[p] (TateModule p J)]
    (hsmul :
    ∀ (a : ℤ_[p]) (x : TateModule p J) (n : ℕ),
    ((a • x : TateModule p J) : ℕ → J) n = (PadicInt.toZModPow n a).val • (x : ℕ → J) n)
    (hfin : Set.Finite {v : J | p • v = 0}) :
    Module.Finite ℤ_[p] (TateModule p J) ∧ Module.Free ℤ_[p] (TateModule p J) := by p2m_exact_reverting @_root_.P2MW.S_W54_finite_free_tateModule.solution
