import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import P2M.Util
import P2M.Sol.S_groupCohomology_Kummer_kummerClass_eq_zero_iff

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer
theorem groupCohomology.Kummer.kummerClass_eq_zero_iff
    {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {p : ℕ} {a : Kˣ} {α : Lˣ} (hα : algebraMap K L (a : K) = (α : L) ^ p) :
    kummerClass hα = 0 ↔ ∃ b : Kˣ, b ^ p = a := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_Kummer_kummerClass_eq_zero_iff.solution
