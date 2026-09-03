import Definitions.Def_LanglandsTunnell_CubicInduction_Growth
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_inv_mul_gauge3_le_norm_vecMul_of_forall_mem_adicCompletionIntegers

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem LanglandsTunnell.CubicInduction.exists_inv_mul_gauge3_le_norm_vecMul_of_forall_mem_adicCompletionIntegers
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (N : ℕ) (hN : 0 < N) (ξ : Fin 3 → ℚ) (hξ : ξ ≠ 0)
    (hint : ∀ (j : Fin 3) (w : HeightOneSpectrum (𝓞 ℚ)),
      ((N : FiniteAdeleRing (𝓞 ℚ) ℚ) *
          (Matrix.vecMul (fun i => algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (ξ i))
            (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) j).2) w ∈ w.adicCompletionIntegers ℚ) :
    ∃ j : Fin 3, ((N : ℝ) * gauge3 ℚ g)⁻¹ ≤
      ‖(Matrix.vecMul (fun i => algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (ξ i))
          (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) j).1 Rat.infinitePlace‖ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_inv_mul_gauge3_le_norm_vecMul_of_forall_mem_adicCompletionIntegers.solution
