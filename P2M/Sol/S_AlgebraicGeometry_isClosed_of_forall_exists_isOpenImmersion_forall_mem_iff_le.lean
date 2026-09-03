import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_isClosed_of_forall_exists_isOpenImmersion_forall_mem_iff_le

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {E : Scheme.{u}} (T : Set E)
    (h : ∀ e : E, ∃ (S : Type u) (_ : CommRing S) (ι : Spec (CommRingCat.of S) ⟶ E) (_ : IsOpenImmersion ι)
        (I : Ideal S), e ∈ Set.range ι.base ∧ ∀ 𝔮 : PrimeSpectrum S, ι.base 𝔮 ∈ T ↔ I ≤ 𝔮.asIdeal) :
    IsClosed T := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨S, _, ι, _, I, ⟨𝔮ₓ, rfl⟩, hiff⟩ := h x
  refine ⟨ι.base '' (PrimeSpectrum.zeroLocus (I : Set S))ᶜ, ?_, ?_, ?_⟩
  · rintro _ ⟨𝔮, h𝔮, rfl⟩ hT
    exact h𝔮 ((PrimeSpectrum.mem_zeroLocus _ _).mpr (SetLike.coe_subset_coe.mpr ((hiff 𝔮).mp hT)))
  · exact ι.isOpenEmbedding.isOpenMap _ (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl
  · exact ⟨𝔮ₓ, fun hz => hx ((hiff 𝔮ₓ).mpr (SetLike.coe_subset_coe.mp ((PrimeSpectrum.mem_zeroLocus _ _).mp hz))), rfl⟩
