import Mathlib
import Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
import P2M.Sol.S_DihedralWeightOne_exists_hasNebentypus_eq_weightOneLift_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm DihedralWeightOne IsDedekindDomain
open scoped MatrixGroups ModularForm

theorem DihedralWeightOne.exists_hasNebentypus_eq_weightOneLift_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul
    {M : ℕ} [NeZero M] (h : CuspForm (CongruenceSubgroup.Gamma1 M) 1)
    {N : ℕ} [NeZero N] (ε : DirichletCharacter ℂ N)
    (y : LocalNewvector.AdelicSpan (weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h)))
    (hy : y ∈ Submodule.span ℂ (Set.range fun u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
      (AdelicDock.finEmbed (𝓞 ℚ) ℚ u : AdelicGL2 (𝓞 ℚ) ℚ) •
        LocalNewvector.AdelicSpan.self (weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h))))
    (hK0 : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (AdelicDock.ratLevel N), ∀ d : ℤ, IsCoprime d (N : ℤ) →
      (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
          - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (d : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (AdelicDock.ratLevel N) →
      ∀ x : AdelicGL2 (𝓞 ℚ) ℚ,
        (LocalNewvector.AdelicSpan.toFn _ y).toFn (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ u) =
          (ε (d : ZMod N))⁻¹ * (LocalNewvector.AdelicSpan.toFn _ y).toFn x) :
    ∃ F : CuspForm (CongruenceSubgroup.Gamma1 N) 1,
      CuspForm.HasNebentypus ε F ∧
      (LocalNewvector.AdelicSpan.toFn _ y).toFn = weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) ∧
      (F = 0 → y = 0) := by p2m_exact_reverting @_root_.P2MW.S_DihedralWeightOne_exists_hasNebentypus_eq_weightOneLift_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul.solution
