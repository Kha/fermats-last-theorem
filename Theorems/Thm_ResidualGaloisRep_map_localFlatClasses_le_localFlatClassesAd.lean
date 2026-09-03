import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_map_localFlatClasses_le_localFlatClassesAd

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem ResidualGaloisRep.map_localFlatClasses_le_localFlatClassesAd
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (ρbar : ResidualGaloisRep k)
    (φ : Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero ⟶
      Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep))
    (hφ : ∀ x : LinearMap.ker (LinearMap.trace k ρbar.V), φ.hom x = (x : Module.End k ρbar.V)) :
    (ρbar.localFlatClasses p).map
        (groupCohomology.map (A := Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero)
          (MonoidHom.id (primeLocalGaloisGroup (pPrime p))) φ 1).hom ≤
      ρbar.localFlatClassesAd p := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_map_localFlatClasses_le_localFlatClassesAd.solution
