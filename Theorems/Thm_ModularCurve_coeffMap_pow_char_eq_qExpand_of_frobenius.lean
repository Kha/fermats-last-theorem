import Definitions.Def_ModularCurve_CoeffSemilinearAut
import P2M.Util
import P2M.Sol.S_ModularCurve_coeffMap_pow_char_eq_qExpand_of_frobenius
attribute [-simp] ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply

set_option autoImplicit false

theorem ModularCurve.coeffMap_pow_char_eq_qExpand_of_frobenius {A k : Type*} [CommRing A] [CommRing k]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (red : A →+* k) (τ : A →+* A)
    (hτ : ∀ a : A, red (τ a) ^ ℓ = red a) (x : LaurentSeries A) :
    ModularCurve.coeffMap red (ModularCurve.coeffMap τ x) ^ ℓ
      = ModularCurve.qExpand k ℓ (ModularCurve.coeffMap red x) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeffMap_pow_char_eq_qExpand_of_frobenius.solution
