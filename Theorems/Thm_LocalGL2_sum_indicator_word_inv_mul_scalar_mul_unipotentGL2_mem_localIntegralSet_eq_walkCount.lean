import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_LocalGL2_sum_indicator_word_inv_mul_scalar_mul_unipotentGL2_mem_localIntegralSet_eq_walkCount

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem LocalGL2.sum_indicator_word_inv_mul_scalar_mul_unipotentGL2_mem_localIntegralSet_eq_walkCount
    (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))
    (ϖ : u.adicCompletionIntegers F) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) ϖ ≠ 0)
    (n : ℕ) (rT : Fin n → GL (Fin 2) (u.adicCompletion F))
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (u.adicCompletionIntegers F) (u.adicCompletion F))
      (LocalGL2.diagPi ϖ hϖ0) rT)
    (z : GL (Fin 2) (u.adicCompletion F))
    (hz : (z : Matrix (Fin 2) (Fin 2) (u.adicCompletion F)) =
      algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) ϖ •
        (1 : Matrix (Fin 2) (Fin 2) (u.adicCompletion F)))
    (W : ℕ → ℕ → ℕ) (h00 : W 0 0 = 1) (h0s : ∀ d : ℕ, W 0 (d + 1) = 0)
    (hroot : ∀ k : ℕ, W (k + 1) 0 = (Ideal.absNorm u.asIdeal + 1) * W k 1)
    (hstep : ∀ k d : ℕ, W (k + 1) (d + 1) = W k d + Ideal.absNorm u.asIdeal * W k (d + 2))
    (k j : ℕ) (t : (u.adicCompletion F)ˣ) (y : u.adicCompletion F)
    (ht : Valued.v (t : u.adicCompletion F) ^ 2 =
      Valued.v (algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) ϖ) ^ (k + 2 * j)) :
    ∑ ι : Fin k → Fin n, (AutomorphicForm.localIntegralSet F u).indicator (fun _ => (1 : ℂ))
        (((List.ofFn fun i => rT (ι i)).prod * z ^ j)⁻¹ *
          (Units.map (Matrix.scalar (Fin 2) :
              u.adicCompletion F →+* Matrix (Fin 2) (Fin 2) (u.adicCompletion F)).toMonoidHom t *
            AutomorphicForm.unipotentGL2 y)) =
      (W k (2 * (WithZero.log (Valued.v y)).toNat) : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_LocalGL2_sum_indicator_word_inv_mul_scalar_mul_unipotentGL2_mem_localIntegralSet_eq_walkCount.solution
