import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_DirichletCharacter_DirichletIdeleChar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_mul_dirichletIdeleChar_det_rightTranslate_invariant_levelOne_sq

set_option autoImplicit false

theorem AutomorphicForm.mul_dirichletIdeleChar_det_rightTranslate_invariant_levelOne_sq
    (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M)
    (φ : GL (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) → ℂ)
    (hK : ∀ (x : GL (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ))
      (k : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)),
      (∀ i j, ((k : Matrix (Fin 2) (Fin 2)
          (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) - 1) i j ∈
        NumberField.AdelicLevel.idealBall (NumberField.RingOfIntegers ℚ) ℚ
          (Ideal.span {(M : NumberField.RingOfIntegers ℚ)})) →
      (∀ i j, (((k⁻¹ : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) :
          Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) - 1) i j ∈
        NumberField.AdelicLevel.idealBall (NumberField.RingOfIntegers ℚ) ℚ
          (Ideal.span {(M : NumberField.RingOfIntegers ℚ)})) →
      φ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ k) = φ x)
    (hT : ∀ (x : GL (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ))
      (u : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ),
      (u : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ∈
        NumberField.AdelicLevel.integralFiniteAdeles (NumberField.RingOfIntegers ℚ) ℚ →
      ((u⁻¹ : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ) :
          IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ∈
        NumberField.AdelicLevel.integralFiniteAdeles (NumberField.RingOfIntegers ℚ) ℚ →
      φ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ (NumberField.AdelicLevel.diagOne u)) =
        χ (RatIdele.unitResidue M (Matrix.GeneralLinearGroup.det
          (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ (NumberField.AdelicLevel.diagOne u)))) *
          φ x)
    (x : GL (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ))
    (k : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ))
    (hk : k ∈ NumberField.AdelicLevel.finiteLevelOne (NumberField.RingOfIntegers ℚ) ℚ
      (Ideal.span {(M : NumberField.RingOfIntegers ℚ)} ^ 2)) :
    φ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ k *
        (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ (NumberField.AdelicLevel.diagOne
          (Units.map (algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) :
            ℚ →* IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)
            (Units.mk0 (M : ℚ) (Nat.cast_ne_zero.mpr (NeZero.ne M)))))⁻¹)) *
        ((DirichletCharacter.dirichletIdeleChar χ (Matrix.GeneralLinearGroup.det
          (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ k)) : ℂˣ) : ℂ) =
      φ (x * (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ (NumberField.AdelicLevel.diagOne
          (Units.map (algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) :
            ℚ →* IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)
            (Units.mk0 (M : ℚ) (Nat.cast_ne_zero.mpr (NeZero.ne M)))))⁻¹)) *
        ((DirichletCharacter.dirichletIdeleChar χ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_mul_dirichletIdeleChar_det_rightTranslate_invariant_levelOne_sq.solution
