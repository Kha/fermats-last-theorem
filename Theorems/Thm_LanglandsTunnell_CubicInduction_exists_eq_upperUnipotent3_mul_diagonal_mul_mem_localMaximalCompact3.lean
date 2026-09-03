import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3
    (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) :
    ∃ (x y z : v.adicCompletion ℚ) (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ),
      ∃ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v,
        (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d ∧
          g = upperUnipotent3 x y z * t * k := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3.solution
