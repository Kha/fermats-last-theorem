import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_pos_forall_mul_prod_le_ideleNorm_det_le_of_isSemiLocalFactorization_of_apply_ne_zero
attribute [-instance] instCountableOfNumberField_definitions

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_pos_forall_mul_prod_le_ideleNorm_det_le_of_isSemiLocalFactorization_of_apply_ne_zero
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L)
    (hϖs : ∀ v ∈ T, Irreducible (ϖs v))
    (hϖs0 : ∀ v ∈ T,
      algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
    (ns : HeightOneSpectrum (𝓞 K) → ℕ)
    (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L))
    (hrTs : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      HeckeIntegralSeam.IsHeckeCosetSystem
        (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
        (LocalGL2.diagPi (ϖs v) (hϖs0 v hv)) (rTs v))
    (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
    (hzs : ∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
      algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) •
        (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L))) :
    ∃ m M : ℝ, 0 < m ∧
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        AutomorphicForm.IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
        ∀ g : GL (Fin 2) (AdeleRing (𝓞 L) L), φ g ≠ 0 →
          m * ∏ v ∈ T, (((Ideal.absNorm (ws v).1.asIdeal : ℕ) : ℝ)⁻¹) ^ (ks v + 2 * js v) ≤
              NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∧
            NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ≤
              M * ∏ v ∈ T, (((Ideal.absNorm (ws v).1.asIdeal : ℕ) : ℝ)⁻¹) ^ (ks v + 2 * js v) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_pos_forall_mul_prod_le_ideleNorm_det_le_of_isSemiLocalFactorization_of_apply_ne_zero.solution
