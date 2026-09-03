import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_isLocallyFlatCocycleAd_zero_of_isLocallyFlatCocycle
attribute [-instance] GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule instIsScalarTowerTensorProduct_definitions
attribute [-simp] GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem ResidualGaloisRep.isLocallyFlatCocycleAd_zero_of_isLocallyFlatCocycle
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ρbar : ResidualGaloisRep k)
    (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero))
    (hc : ρbar.IsLocallyFlatCocycle p c) :
    ρbar.IsLocallyFlatCocycleAd p 0 := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_isLocallyFlatCocycleAd_zero_of_isLocallyFlatCocycle.solution
