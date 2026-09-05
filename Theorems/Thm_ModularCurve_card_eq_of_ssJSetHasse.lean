module

public import Mathlib
public import Definitions.Def_WeierstrassCurve_HasseInvariant
public import Definitions.Def_ModularCurve_JWidth
public import P2M.Util
public import P2M.Sol.S_ModularCurve_card_eq_of_ssJSetHasse

@[expose] public section

open ModularCurve
theorem ModularCurve.card_eq_of_ssJSetHasse (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K q] [DecidableEq K]
    (S : Finset K) (hS : ∀ j, j ∈ S ↔ j ∈ ssJSetHasse q K) :
    S.card = q / 12 + (if q % 3 = 2 then 1 else 0) + (if q % 4 = 3 then 1 else 0) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_card_eq_of_ssJSetHasse.solution
