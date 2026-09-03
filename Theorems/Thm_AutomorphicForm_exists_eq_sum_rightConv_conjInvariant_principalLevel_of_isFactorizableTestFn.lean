import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_PrincipalLevel
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_eq_sum_rightConv_conjInvariant_principalLevel_of_isFactorizableTestFn
attribute [-instance] AutomorphicForm.GaussTwist.instFiniteLocalGaussFactorValHeightOneSpectrumRingOfIntegersMemFinsetModulusPrimes AutomorphicForm.GaussTwist.instFintypeGaussIndex AutomorphicForm.GaussTwist.instCommGroupGaussIndex AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm IsDedekindDomain

theorem AutomorphicForm.exists_eq_sum_rightConv_conjInvariant_principalLevel_of_isFactorizableTestFn
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (hf : IsFactorizableTestFn K f)
    (hfU : ∀ x : GL (Fin 2) (AdeleRing (𝓞 K) K),
      ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, f (x * u) = f x) :
    ∃ (n : ℕ) (fs gs : Fin n → GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ),
      (∀ k, IsFactorizableTestFn K (fs k)) ∧
      (∀ k, Continuous (gs k) ∧ HasCompactSupport (gs k) ∧
        IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (gs k) ∧
        (∀ (w : InfinitePlace K) (κ : rowIsometrySubgroup₀ w.Completion)
            (x : GL (Fin 2) (AdeleRing (𝓞 K) K)),
          gs k (rowIsometryInclAt₀ K w κ * x * (rowIsometryInclAt₀ K w κ)⁻¹) = gs k x) ∧
        (∀ x : GL (Fin 2) (AdeleRing (𝓞 K) K), gs k x ≠ 0 →
          ∃ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
            glFin (𝓞 K) K u = glFin (𝓞 K) K x)) ∧
      ∀ x : GL (Fin 2) (AdeleRing (𝓞 K) K), f x = ∑ k, rightConv K (fs k) (fun y => gs k y⁻¹) x := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_eq_sum_rightConv_conjInvariant_principalLevel_of_isFactorizableTestFn.solution
