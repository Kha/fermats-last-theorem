import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_snd_apply_eq_zero_of_mem_minimalPrimes_of_isMaximal

set_option autoImplicit false

theorem Ideal.snd_apply_eq_zero_of_mem_minimalPrimes_of_isMaximal
    (L : Type) [Field L] [CharZero L] (R : Type) [CommRing R] [Algebra L R] [IsReduced R]
    (𝔭 : Ideal R) (h𝔭 : 𝔭 ∈ (⊥ : Ideal R).minimalPrimes) (h𝔭' : 𝔭.IsMaximal)
    [Module.Finite L (R ⧸ 𝔭)]
    (K : Type) [Field K] [Algebra L K]
    (φ : R →ₐ[L] DualNumber K)
    (hφ : RingHom.ker ((TrivSqZeroExt.fstHom L K K).comp φ).toRingHom = 𝔭) :
    ∀ r : R, (φ r).snd = 0 := by p2m_exact_reverting @_root_.P2MW.S_Ideal_snd_apply_eq_zero_of_mem_minimalPrimes_of_isMaximal.solution
