import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import P2M.Util
import P2M.Sol.S_ModularCurve_tateBase_mul_eq_map_qExpand_and_tateToricPoint_eq_and_nonToricPoint_eq

set_option autoImplicit false

universe u

open ModularCurve

theorem ModularCurve.tateBase_mul_eq_map_qExpand_and_tateToricPoint_eq_and_nonToricPoint_eq
    (K : Type u) [CommRing K] (p N : ℕ) [NeZero p] [NeZero N] :
    haveI : NeZero (N * p) := ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne p)⟩
    ModularCurve.tateBase K (N * p) = (ModularCurve.tateBase K p).map (ModularCurve.qExpand K N) ∧
    (∀ c : Kˣ,
      (ModularCurve.tateToricPoint K (N * p) c).1 = ModularCurve.qExpand K N (ModularCurve.tateToricPoint K p c).1 ∧
      (ModularCurve.tateToricPoint K (N * p) c).2 = ModularCurve.qExpand K N (ModularCurve.tateToricPoint K p c).2) ∧
    (∀ (c : Kˣ) (j : ℕ), 0 < j → j < p →
      (ModularCurve.nonToricPoint K (N * p) c (N * j)).1 = ModularCurve.qExpand K N (ModularCurve.nonToricPoint K p c j).1 ∧
      (ModularCurve.nonToricPoint K (N * p) c (N * j)).2 = ModularCurve.qExpand K N (ModularCurve.nonToricPoint K p c j).2) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_tateBase_mul_eq_map_qExpand_and_tateToricPoint_eq_and_nonToricPoint_eq.solution
