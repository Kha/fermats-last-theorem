import Mathlib
import P2M.Util
import P2M.Sol.S_HomogeneousLocalization_Away_flat_quotientMk_comp_of_forall_flat_piece

set_option autoImplicit false

universe u v

open HomogeneousLocalization

theorem HomogeneousLocalization.Away.flat_quotientMk_comp_of_forall_flat_piece
    {S : Type u} [CommRing S] {A : Type v} [CommRing A] [Algebra S A]
    (𝒜 : ℕ → Submodule S A) [GradedAlgebra 𝒜]
    (I : Ideal A) (hI : ∀ a ∈ I, ∀ k : ℕ, (DirectSum.decompose 𝒜 a k : A) ∈ I)
    (hflat : ∀ k : ℕ, Module.Flat S (↥(𝒜 k) ⧸ Submodule.comap (𝒜 k).subtype (I.restrictScalars S)))
    {d : ℕ} (f : A) (hf : f ∈ 𝒜 d) :
    ((Ideal.Quotient.mk (Ideal.span {x : Away 𝒜 f |
          ∃ y : NumDenSameDeg 𝒜 (Submonoid.powers f), (y.num : A) ∈ I ∧ HomogeneousLocalization.mk y = x})).comp
      ((HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f)).comp
        ((GradedRing.projZeroRingHom' 𝒜).comp (algebraMap S A)))).Flat := by p2m_exact_reverting @_root_.P2MW.S_HomogeneousLocalization_Away_flat_quotientMk_comp_of_forall_flat_piece.solution
