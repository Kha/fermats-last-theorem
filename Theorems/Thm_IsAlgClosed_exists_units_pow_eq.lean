import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import P2M.Util
import P2M.Sol.S_IsAlgClosed_exists_units_pow_eq

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer
theorem IsAlgClosed.exists_units_pow_eq
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {n : ℕ} (hn : 0 < n) (x : Ωˣ) :
    ∃ y : Ωˣ, y ^ n = x := by p2m_exact_reverting @_root_.P2MW.S_IsAlgClosed_exists_units_pow_eq.solution
