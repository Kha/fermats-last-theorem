import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import P2M.Util
import P2M.Sol.S_CuspForm_IsAdelicLiftOfGamma1_exists_hasNebentypus_isAdelicLiftOfGamma1_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul

set_option autoImplicit false

theorem CuspForm.IsAdelicLiftOfGamma1.exists_hasNebentypus_isAdelicLiftOfGamma1_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul
    {M : ℕ} [NeZero M] {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ}
    (hΦh : CuspForm.IsAdelicLiftOfGamma1 h Φ)
    {N : ℕ} [NeZero N] (ε : DirichletCharacter ℂ N)
    (y : LocalNewvector.AdelicSpan Φ)
    (hy : y ∈ Submodule.span ℂ (Set.range fun u :
      GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) =>
        (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ u :
          AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) • LocalNewvector.AdelicSpan.self Φ))
    (hK0 : ∀ u ∈ NumberField.AdelicLevel.finiteLevelZero (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.ratLevel N),
      ∀ d : ℤ, IsCoprime d (N : ℤ) →
        (u : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) 1 1
            - algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) (d : ℚ)
          ∈ NumberField.AdelicLevel.idealBall (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.ratLevel N) →
        ∀ x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
          (LocalNewvector.AdelicSpan.toFn Φ y).toFn (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ u)
            = (ε (d : ZMod N))⁻¹ * (LocalNewvector.AdelicSpan.toFn Φ y).toFn x) :
    ∃ F : CuspForm (CongruenceSubgroup.Gamma1 N) 2,
      CuspForm.HasNebentypus ε F ∧
      CuspForm.IsAdelicLiftOfGamma1 F (LocalNewvector.AdelicSpan.toFn Φ y).toFn ∧
      (F = 0 → y = 0) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsAdelicLiftOfGamma1_exists_hasNebentypus_isAdelicLiftOfGamma1_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul.solution
