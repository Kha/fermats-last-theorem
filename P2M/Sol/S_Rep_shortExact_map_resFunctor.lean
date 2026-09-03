import Mathlib
import P2M.Util
namespace P2MW.S_Rep_shortExact_map_resFunctor

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem solution {k G H : Type u} [CommRing k] [Group G] [Group H] (f : H →* G)
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) :
    (X.map (Rep.resFunctor f)).ShortExact where
  exact := (forget₂ (Rep.{u} k H) (ModuleCat k)).reflects_exact_of_faithful _
    ((ShortComplex.moduleCat_exact_iff _).2 fun x hx => by
      have h := (hX.exact.map (forget₂ (Rep.{u} k G) (ModuleCat k))).moduleCat_range_eq_ker
      have hx' : x ∈ LinearMap.ker (ModuleCat.Hom.hom (X.map (forget₂ (Rep.{u} k G) (ModuleCat k))).g) := hx
      rw [← h] at hx'
      obtain ⟨a, ha⟩ := hx'
      exact ⟨a, ha⟩)
  mono_f := (Rep.mono_iff_injective _).2 ((Rep.mono_iff_injective X.f).1 hX.mono_f)
  epi_g := (Rep.epi_iff_surjective _).2 ((Rep.epi_iff_surjective X.g).1 hX.epi_g)
