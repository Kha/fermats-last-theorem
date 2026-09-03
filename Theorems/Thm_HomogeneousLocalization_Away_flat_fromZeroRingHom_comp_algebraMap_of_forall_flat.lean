import Mathlib
import P2M.Util
import P2M.Sol.S_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat

set_option autoImplicit false

universe u v

open HomogeneousLocalization

theorem HomogeneousLocalization.Away.flat_fromZeroRingHom_comp_algebraMap_of_forall_flat
    {S : Type u} [CommRing S] {A : Type v} [CommRing A] [Algebra S A]
    (𝒜 : ℕ → Submodule S A) [GradedAlgebra 𝒜]
    (hflat : ∀ n : ℕ, Module.Flat S (𝒜 n))
    {d : ℕ} (f : A) (hf : f ∈ 𝒜 d) :
    ((HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f)).comp
        ((GradedRing.projZeroRingHom' 𝒜).comp (algebraMap S A))).Flat := by p2m_exact_reverting @_root_.P2MW.S_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat.solution
