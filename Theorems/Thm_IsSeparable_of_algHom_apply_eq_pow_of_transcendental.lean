import Mathlib
import P2M.Util
import P2M.Sol.S_IsSeparable_of_algHom_apply_eq_pow_of_transcendental

set_option autoImplicit false

theorem IsSeparable.of_algHom_apply_eq_pow_of_transcendental
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    (p r : ℕ) [Fact p.Prime] [CharP F p] (hr : 0 < r)
    (φ : F →ₐ[K] F) (t : F) (ht : Transcendental K t) (hφt : φ t = t ^ p ^ r)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F)
    (g : F) (hg : φ g = g ^ p ^ r) :
    IsSeparable (Subfield.closure ({c : F | c ^ p ^ r = c} ∪ {t})) g := by p2m_exact_reverting @_root_.P2MW.S_IsSeparable_of_algHom_apply_eq_pow_of_transcendental.solution
