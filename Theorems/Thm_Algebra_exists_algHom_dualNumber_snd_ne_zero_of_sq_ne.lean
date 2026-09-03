import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_algHom_dualNumber_snd_ne_zero_of_sq_ne

set_option autoImplicit false

theorem Algebra.exists_algHom_dualNumber_snd_ne_zero_of_sq_ne
    (Ω : Type*) [Field Ω] (S : Type*) [CommRing S] [Algebra Ω S]
    (𝔪 : Ideal S) [𝔪.IsMaximal] (hres : Function.Surjective (algebraMap Ω (S ⧸ 𝔪)))
    (hne : 𝔪 ^ 2 ≠ 𝔪) :
    ∃ (φ : S →ₐ[Ω] DualNumber Ω) (s : S), TrivSqZeroExt.snd (φ s) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_algHom_dualNumber_snd_ne_zero_of_sq_ne.solution
