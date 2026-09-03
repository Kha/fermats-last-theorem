import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import P2M.Util
import P2M.Sol.S_groupCohomology_Kummer_natCard_H1_eq_natCard_quotient

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer
theorem groupCohomology.Kummer.natCard_H1_eq_natCard_quotient
    {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (p : ℕ) :
    Nat.card (H1 (kummerRep K L p))
      = Nat.card (powerSubgroup K L p ⧸
          ((powMonoidHom p : Kˣ →* Kˣ).range).subgroupOf (powerSubgroup K L p)) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_Kummer_natCard_H1_eq_natCard_quotient.solution
