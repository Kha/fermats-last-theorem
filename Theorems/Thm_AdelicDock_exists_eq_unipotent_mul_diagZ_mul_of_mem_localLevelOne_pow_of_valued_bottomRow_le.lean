import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
import P2M.Sol.S_AdelicDock_exists_eq_unipotent_mul_diagZ_mul_of_mem_localLevelOne_pow_of_valued_bottomRow_le

set_option autoImplicit false

open IsDedekindDomain NumberField AdelicDock UnramifiedWhittaker

theorem AdelicDock.exists_eq_unipotent_mul_diagZ_mul_of_mem_localLevelOne_pow_of_valued_bottomRow_le
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (ϖ : v.adicCompletionIntegers F) (hπ : (ϖ : v.adicCompletion F) ≠ 0)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1 : ℤ))
    (m : ℕ) (hm : 1 ≤ m) (g : GL (Fin 2) (v.adicCompletion F))
    (hc : Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0) ≤ WithZero.exp (-(m : ℤ)))
    (hd : Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 - 1) ≤ WithZero.exp (-(m : ℤ))) :
    ∃ (x : v.adicCompletion F) (n : ℤ) (k : GL (Fin 2) (v.adicCompletion F)),
      k ∈ localLevelOne (𝓞 F) F v (v.asIdeal ^ m) ∧
      g = unipotent x * diagZ (ϖ : v.adicCompletion F) hπ n * k ∧
      Valued.v (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det = WithZero.exp (-n) := by p2m_exact_reverting @_root_.P2MW.S_AdelicDock_exists_eq_unipotent_mul_diagZ_mul_of_mem_localLevelOne_pow_of_valued_bottomRow_le.solution
