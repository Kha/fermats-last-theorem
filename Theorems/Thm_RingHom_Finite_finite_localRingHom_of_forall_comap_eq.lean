import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_Finite_finite_localRingHom_of_forall_comap_eq

set_option autoImplicit false
theorem RingHom.Finite.finite_localRingHom_of_forall_comap_eq
    {B C : Type*} [CommRing B] [CommRing C] (φ : B →+* C) (hφ : φ.Finite)
    (𝔮 : Ideal C) [𝔮.IsPrime]
    (huniq : ∀ Q : Ideal C, Q.IsPrime → Q.comap φ = 𝔮.comap φ → Q = 𝔮) :
    (Localization.localRingHom (𝔮.comap φ) 𝔮 φ rfl).Finite := by p2m_exact_reverting @_root_.P2MW.S_RingHom_Finite_finite_localRingHom_of_forall_comap_eq.solution
