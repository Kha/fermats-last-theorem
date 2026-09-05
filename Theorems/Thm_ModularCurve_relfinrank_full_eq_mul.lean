module

public import Definitions.Def_ModularCurve_X0
public import Mathlib.FieldTheory.Relrank
import P2M.Util
import P2M.Sol.S_ModularCurve_relfinrank_full_eq_mul

@[expose] public section

open ModularCurve
theorem ModularCurve.relfinrank_full_eq_mul (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (a : ℕ) (hup : modularFunctionFieldFull (M * p ^ (a + 1)) = IntermediateField.adjoin ℚ (insert (jqN (p ^ (a + 1))) (modularFunctionFieldFull (M * p ^ a) : Set (LaurentSeries ℚ)))) (hnm : jqN (p ^ (a + 1)) ∉ modularFunctionFieldFull (M * p ^ a)) : IntermediateField.relfinrank (modularFunctionFieldFull (M * p ^ a)) (modularFunctionFieldFull (M * p ^ (a + 1))) = if a = 0 then p + 1 else p := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_relfinrank_full_eq_mul.solution
