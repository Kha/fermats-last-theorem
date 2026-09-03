import Mathlib
import Definitions.Def_GroupCohomology_SplittingModule
import P2M.Util
import Definitions.Def_Compat_Mathlib430
namespace P2MW.S_Rep_augShortComplex_shortExact

set_option autoImplicit false
universe u
open CategoryTheory Rep

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

theorem solution (k G : Type u) [CommRing k] [Group G] :
    (Rep.augShortComplex k G).ShortExact where
  exact := (forget₂ (Rep k G) (ModuleCat k)).reflects_exact_of_faithful _ <|
    (ShortComplex.moduleCat_exact_iff _).2 fun f hf => ⟨⟨f, LinearMap.mem_ker.2 hf⟩, rfl⟩
  mono_f := (Rep.mono_iff_injective _).2 Subtype.val_injective
  epi_g := (Rep.epi_iff_surjective _).2 fun r =>
    ⟨Finsupp.single 1 r, by
      change (Rep.augε k G).hom (Finsupp.single 1 r) = r
      rw [Rep.leftRegularHomFinsupp_hom_single, Rep.trivial_ρ_apply, smul_eq_mul, mul_one]⟩
