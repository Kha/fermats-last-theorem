import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import P2M.Util
import P2M.Sol.S_groupCohomology_Kummer_kummerHom_surjective

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer
theorem groupCohomology.Kummer.kummerHom_surjective
    {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (p : ℕ) :
    Function.Surjective (kummerHom K L p) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_Kummer_kummerHom_surjective.solution
