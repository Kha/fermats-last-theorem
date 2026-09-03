import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import P2M.Util
import P2M.Sol.S_groupCohomology_Kummer_ker_kummerHom

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer
theorem groupCohomology.Kummer.ker_kummerHom
    {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L] (p : ℕ) :
    (kummerHom K L p).ker
      = ((powMonoidHom p : Kˣ →* Kˣ).range).subgroupOf (powerSubgroup K L p) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_Kummer_ker_kummerHom.solution
