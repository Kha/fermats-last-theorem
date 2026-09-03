import Mathlib
import P2M.Util
import P2M.Sol.S_KaehlerDifferential_exists_eq_smul_D_of_retraction_of_ker_le_span_sup_sq

set_option autoImplicit false

theorem KaehlerDifferential.exists_eq_smul_D_of_retraction_of_ker_le_span_sup_sq
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing S] [Module.Finite S Ω[S⁄R]]
    (π : S →ₐ[R] R) (t : S) (ht : π t = 0)
    (hcot : RingHom.ker π.toRingHom ≤ Ideal.span {t} ⊔ RingHom.ker π.toRingHom ^ 2)
    (ω : Ω[S⁄R]) :
    ∃ g : S, ω = g • KaehlerDifferential.D R S t := by p2m_exact_reverting @_root_.P2MW.S_KaehlerDifferential_exists_eq_smul_D_of_retraction_of_ker_le_span_sup_sq.solution
