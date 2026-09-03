import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_finset_localMaximalCompact3_eq_mul_of_level_le
attribute [-simp] LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.exists_finset_localMaximalCompact3_eq_mul_of_level_le
    (v : HeightOneSpectrum (𝓞 ℚ)) (n m : ℕ) (hnm : n ≤ m) (hm : 1 ≤ m) :
    ∃ S : Finset (LocalGL3 v),
      (∀ s ∈ S, s ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧ ∀ i j : Fin 3,
        Valued.v (gl3Entry v s i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
          ≤ WithZero.exp (-(n : ℤ))) ∧
      ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v,
        (∀ i j : Fin 3,
          Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
            ≤ WithZero.exp (-(n : ℤ))) →
        ∃! s, s ∈ S ∧ ∃ κ : LocalGL3 v,
          (∀ i j : Fin 3,
            Valued.v (gl3Entry v κ i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
              ≤ WithZero.exp (-(m : ℤ))) ∧
          k = s * κ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_finset_localMaximalCompact3_eq_mul_of_level_le.solution
