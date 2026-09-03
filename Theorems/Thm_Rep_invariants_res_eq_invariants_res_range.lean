import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_invariants_res_eq_invariants_res_range

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical TensorProduct

theorem Rep.invariants_res_eq_invariants_res_range
    {k : Type} [CommRing k] {G D' : Type} [Group G] [Group D'] (φ : D' →* G) (X : Rep.{0} k G) :
    (Rep.res φ X).ρ.invariants = (Rep.res φ.range.subtype X).ρ.invariants := by p2m_exact_reverting @_root_.P2MW.S_Rep_invariants_res_eq_invariants_res_range.solution
