import Mathlib
import Definitions.Def_GroupCohomology_SplittingModule
import P2M.Util
namespace P2MW.S_Rep_splittingShortComplex_shortExact

set_option autoImplicit false
universe u
open CategoryTheory Rep

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

theorem solution {k G : Type u} [CommRing k] [Group G]
    (C : Rep.{u} k G) (φ : groupCohomology.cocycles₂ C) :
    (Rep.splittingShortComplex C φ).ShortExact where
  exact := (forget₂ (Rep k G) (ModuleCat k)).reflects_exact_of_faithful _ <|
    (ShortComplex.moduleCat_exact_iff _).2 fun v hv => ⟨v.1, Prod.ext rfl (Eq.symm hv)⟩
  mono_f := (Rep.mono_iff_injective _).2 LinearMap.inl_injective
  epi_g := (Rep.epi_iff_surjective _).2 fun y => ⟨((0 : C), y), rfl⟩
