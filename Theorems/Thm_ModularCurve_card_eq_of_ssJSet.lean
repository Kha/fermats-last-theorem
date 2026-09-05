module

public import Mathlib
public import Definitions.Def_ModularCurve_SupersingularModuli
import P2M.Util
import P2M.Sol.S_ModularCurve_card_eq_of_ssJSet

@[expose] public section

open ModularCurve
namespace ModularCurve
theorem card_eq_of_ssJSet (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K q] [DecidableEq K]
    (S : Finset K) (hS : ∀ j, j ∈ S ↔ j ∈ ssJSet q K) :
    S.card = q / 12 + (if q % 3 = 2 then 1 else 0) + (if q % 4 = 3 then 1 else 0) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_card_eq_of_ssJSet.solution
end ModularCurve
