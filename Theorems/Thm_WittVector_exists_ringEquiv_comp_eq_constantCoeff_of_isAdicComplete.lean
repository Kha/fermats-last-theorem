import Mathlib
import P2M.Util
import P2M.Sol.S_WittVector_exists_ringEquiv_comp_eq_constantCoeff_of_isAdicComplete

universe u v

theorem WittVector.exists_ringEquiv_comp_eq_constantCoeff_of_isAdicComplete
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {k : Type v} [CommRing k] [CharP k p] [PerfectRing k p] [Algebra 𝓞 k]
    (hk : Function.Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] :
    ∃ e : WittVector p k ≃+* 𝓞,
      (algebraMap 𝓞 k).comp e.toRingHom = WittVector.constantCoeff ∧
      ∀ g : WittVector p k →+* 𝓞,
        (algebraMap 𝓞 k).comp g = WittVector.constantCoeff → g = e.toRingHom := by p2m_exact_reverting @_root_.P2MW.S_WittVector_exists_ringEquiv_comp_eq_constantCoeff_of_isAdicComplete.solution
