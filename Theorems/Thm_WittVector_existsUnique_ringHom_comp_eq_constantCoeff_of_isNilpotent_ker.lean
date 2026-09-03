import Mathlib
import P2M.Util
import P2M.Sol.S_WittVector_existsUnique_ringHom_comp_eq_constantCoeff_of_isNilpotent_ker

set_option autoImplicit false

universe u

theorem WittVector.existsUnique_ringHom_comp_eq_constantCoeff_of_isNilpotent_ker
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
    (B : Type u) [CommRing B] (ρ : B →+* k) (hρ : Function.Surjective ρ) (hnil : IsNilpotent (RingHom.ker ρ)) :
    ∃! f : WittVector p k →+* B, ρ.comp f = WittVector.constantCoeff := by p2m_exact_reverting @_root_.P2MW.S_WittVector_existsUnique_ringHom_comp_eq_constantCoeff_of_isNilpotent_ker.solution
