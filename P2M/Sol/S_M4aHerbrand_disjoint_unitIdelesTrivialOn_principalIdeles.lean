import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import P2M.Util
namespace P2MW.S_M4aHerbrand_disjoint_unitIdelesTrivialOn_principalIdeles

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand CategoryTheory

open NumberField IsDedekindDomain M4aHerbrand in
theorem solution
    (F : Type) [Field F] [NumberField F] (T : Set (HeightOneSpectrum (𝓞 F))) :
    Disjoint (unitIdelesTrivialOn (𝓞 F) F T) (principalIdeles (𝓞 F) F) := by
  rw [disjoint_iff, eq_bot_iff]
  rintro x ⟨hxU, hxP⟩
  rw [Subgroup.mem_bot]
  obtain ⟨k, rfl⟩ := hxP

  have hinf : infPart (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) k) = 1 :=
    ((mem_unitIdelesTrivialOn_iff T _).mp hxU).2.1
  have hk : (algebraMap F (AdeleRing (𝓞 F) F) (k : F)).1 = 1 := by
    have := congrArg (fun u : (InfiniteAdeleRing F)ˣ => (u : InfiniteAdeleRing F)) hinf
    simp only [coe_infPart_apply, Units.coe_map, MonoidHom.coe_coe, Units.val_one] at this
    exact this
  have hk1 : (k : F) = 1 := (algebraMap F (InfiniteAdeleRing F)).injective (by
    change (algebraMap F (AdeleRing (𝓞 F) F) (k : F)).1 = _
    rw [hk, map_one])
  apply Units.ext
  rw [Units.coe_map, MonoidHom.coe_coe, hk1, map_one, Units.val_one]
