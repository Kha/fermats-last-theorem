import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import P2M.Util
import P2M.Sol.S_groupCohomology_Kummer_exists_kummerClass_eq

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer
theorem groupCohomology.Kummer.exists_kummerClass_eq
    {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {p : ℕ} (x : H1 (kummerRep K L p)) :
    ∃ (a : Kˣ) (α : Lˣ) (hα : algebraMap K L (a : K) = (α : L) ^ p), x = kummerClass hα := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_Kummer_exists_kummerClass_eq.solution
