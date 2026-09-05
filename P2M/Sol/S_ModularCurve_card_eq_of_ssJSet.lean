module

public import Definitions.Def_ModularCurve_SupersingularModuli
import P2M.Sol.S_ModularCurve_ssJSet_eq_ssJSetHasse
import P2M.Sol.S_ModularCurve_card_eq_of_ssJSetHasse
import P2M.Util
public import Mathlib.FieldTheory.IsAlgClosed.Basic

namespace P2MW.S_ModularCurve_card_eq_of_ssJSet

set_option autoImplicit false

open ModularCurve

theorem solution (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K q] [DecidableEq K]
    (S : Finset K) (hS : ∀ j, j ∈ S ↔ j ∈ ssJSet q K) :
    S.card = q / 12 + (if q % 3 = 2 then 1 else 0) + (if q % 4 = 3 then 1 else 0) := by
  have hq2 : q ≠ 2 := by omega
  refine card_eq_of_ssJSetHasse q hq K S fun j => ?_
  rw [hS, ssJSet_eq_ssJSetHasse q hq2 K]
end S_ModularCurve_card_eq_of_ssJSet
end P2MW

public section
open ModularCurve
namespace ModularCurve
theorem card_eq_of_ssJSet (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K q] [DecidableEq K]
    (S : Finset K) (hS : ∀ j, j ∈ S ↔ j ∈ ssJSet q K) :
    S.card = q / 12 + (if q % 3 = 2 then 1 else 0) + (if q % 4 = 3 then 1 else 0) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_card_eq_of_ssJSet.solution
end ModularCurve
end
