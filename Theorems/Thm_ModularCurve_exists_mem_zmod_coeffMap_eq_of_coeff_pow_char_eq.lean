import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_mem_zmod_coeffMap_eq_of_coeff_pow_char_eq
set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_mem_zmod_coeffMap_eq_of_coeff_pow_char_eq
    {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] (gbar : ↥(modularFunctionFieldC k N))
    (hfix : ∀ n : ℤ, ((gbar : LaurentSeries k).coeff n) ^ q = (gbar : LaurentSeries k).coeff n) :
    ∃ h₀ : ↥(modularFunctionFieldC (ZMod q) N),
      coeffMap (ZMod.castHom (dvd_refl q) k) (h₀ : LaurentSeries (ZMod q)) = (gbar : LaurentSeries k) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_mem_zmod_coeffMap_eq_of_coeff_pow_char_eq.solution
