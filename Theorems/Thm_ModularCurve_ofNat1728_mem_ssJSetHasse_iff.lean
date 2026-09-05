module

public import Mathlib
public import Definitions.Def_WeierstrassCurve_HasseInvariant
public import P2M.Util
public import P2M.Sol.S_ModularCurve_ofNat1728_mem_ssJSetHasse_iff

@[expose] public section

open ModularCurve
theorem ModularCurve.ofNat1728_mem_ssJSetHasse_iff (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (K : Type*)
    [Field K] [IsAlgClosed K] [CharP K q] : (1728 : K) ∈ ssJSetHasse q K ↔ q % 4 = 3 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ofNat1728_mem_ssJSetHasse_iff.solution
