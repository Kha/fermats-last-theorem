import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_finite_of_isLocallyFlatCocycleAd_zero

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem ResidualGaloisRep.finite_of_isLocallyFlatCocycleAd_zero
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (ρbar : ResidualGaloisRep k)
    (hflat : ρbar.IsLocallyFlatCocycleAd p 0) : Finite k := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_finite_of_isLocallyFlatCocycleAd_zero.solution
