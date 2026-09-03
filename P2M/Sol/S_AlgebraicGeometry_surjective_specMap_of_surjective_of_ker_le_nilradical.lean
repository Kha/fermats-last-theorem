import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_surjective_specMap_of_surjective_of_ker_le_nilradical

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Surjective f)
    (hker : RingHom.ker f ≤ nilradical R) :
    Surjective (Spec.map (CommRingCat.ofHom f)) := by
  have h := PrimeSpectrum.isHomeomorph_comap f (fun x => ⟨1, one_pos, by simpa using hf x⟩) hker
  exact ⟨fun x => by
    obtain ⟨y, hy⟩ := h.surjective x
    exact ⟨y, hy⟩⟩
