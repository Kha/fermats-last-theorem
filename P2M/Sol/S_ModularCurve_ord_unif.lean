import Mathlib
import Definitions.Def_ModularCurve_SSCarrier
import P2M.Util
namespace P2MW.S_ModularCurve_ord_unif

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem solution (K : Type) [Field K] (N : ℕ) [NeZero N]
    (x : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N)) : x.ord (ModularCurve.unif N K x) = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible x.toValuationSubring
  exact Classical.epsilon_spec (p := fun π : ↥(modularFunctionFieldC K N) => x.ord π = 1)
    ⟨(π : ↥(modularFunctionFieldC K N)), x.ord_coe_irreducible hπ⟩
