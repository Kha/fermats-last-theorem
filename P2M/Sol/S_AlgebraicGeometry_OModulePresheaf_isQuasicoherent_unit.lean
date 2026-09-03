import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_unit

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R)) :
    (OModulePresheaf.unit π).IsQuasicoherent := by
  intro U f
  haveI hloc : IsLocalization.Away f Γ(V, V.basicOpen f) := U.2.isLocalization_basicOpen f
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · obtain ⟨⟨y, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f) (show Γ(V, V.basicOpen f) from x)
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    refine ⟨n, y, ?_⟩
    show (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom y
      = (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ n) * (show Γ(V, V.basicOpen f) from x)
    have e1 : (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom y = algebraMap Γ(V, ↑U) Γ(V, V.basicOpen f) y := rfl
    have e2 : (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ n)
        = algebraMap Γ(V, ↑U) Γ(V, V.basicOpen f) (s : Γ(V, ↑U)) := by rw [← hn]; rfl
    rw [e1, e2, ← hs, mul_comm]
  · have hy' : algebraMap Γ(V, ↑U) Γ(V, V.basicOpen f) (show Γ(V, ↑U) from y) = 0 := hy
    obtain ⟨⟨m, hm⟩, hmy⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) _ _).mp hy'
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hm
    exact ⟨n, hmy⟩
