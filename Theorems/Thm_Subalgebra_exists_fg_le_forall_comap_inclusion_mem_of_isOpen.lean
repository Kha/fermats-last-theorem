import Mathlib
import P2M.Util
import P2M.Sol.S_Subalgebra_exists_fg_le_forall_comap_inclusion_mem_of_isOpen

set_option autoImplicit false

universe u

theorem Subalgebra.exists_fg_le_forall_comap_inclusion_mem_of_isOpen
    {S : Type u} [CommRing S] (S₀ : Subalgebra ℤ S) (h₀ : S₀.FG)
    (U : Set (PrimeSpectrum ↥S₀)) (hU : IsOpen U)
    (hUS : ∀ p : PrimeSpectrum S, PrimeSpectrum.comap (algebraMap ↥S₀ S) p ∈ U) :
    ∃ (S₁ : Subalgebra ℤ S) (h : S₀ ≤ S₁), S₁.FG ∧
      ∀ q : PrimeSpectrum ↥S₁, PrimeSpectrum.comap (Subalgebra.inclusion h).toRingHom q ∈ U := by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_exists_fg_le_forall_comap_inclusion_mem_of_isOpen.solution
