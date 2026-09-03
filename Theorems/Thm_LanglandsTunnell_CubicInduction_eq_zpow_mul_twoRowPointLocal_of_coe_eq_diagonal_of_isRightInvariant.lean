import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_eq_zpow_mul_twoRowPointLocal_of_coe_eq_diagonal_of_isRightInvariant

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.eq_zpow_mul_twoRowPointLocal_of_coe_eq_diagonal_of_isRightInvariant
    (v : HeightOneSpectrum (𝓞 ℚ)) (W : LocalGL3 v → ℂ) (e₃ : ℂ)
    (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (hZ : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ)
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d)
    (k₁ k₂ : ℕ) (c : ℤ)
    (h0 : Valued.v (d 0) = WithZero.exp (-((k₁ : ℤ) + c)))
    (h1 : Valued.v (d 1) = WithZero.exp (-((k₂ : ℤ) + c)))
    (h2 : Valued.v (d 2) = WithZero.exp (-c)) :
    W t = e₃ ^ c * W (twoRowPointLocal v k₁ k₂) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_eq_zpow_mul_twoRowPointLocal_of_coe_eq_diagonal_of_isRightInvariant.solution
