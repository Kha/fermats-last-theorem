import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange
universe u v

open scoped TensorProduct in
theorem HopfAlgebra.exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {H₀ : Type v} [CommRing H₀] [HopfAlgebra R H₀] [Module.Finite R H₀] [Module.Flat R H₀]
    [Coalgebra.IsCocomm R H₀]
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
    [Coalgebra.IsCocomm R H]
    (lam : (K ⊗[R] H₀) ≃ₐ[K] (K ⊗[R] H))
    (hlam_comul : ∀ x, Coalgebra.comul (R := K) (lam x) =
      (TensorProduct.map lam.toLinearMap lam.toLinearMap) (Coalgebra.comul (R := K) x))
    (hlam_counit : ∀ x, Coalgebra.counit (R := K) (lam x) = Coalgebra.counit (R := K) x) :
    ∃ (C : Type v) (_ : CommRing C) (_ : HopfAlgebra R C) (_ : Module.Finite R C)
      (_ : Module.Flat R C) (_ : Coalgebra.IsCocomm R C)
      (j₀ : H₀ →ₐc[R] C) (j : H →ₐc[R] C),
      Function.Injective j₀ ∧ Function.Injective j ∧
      Function.Surjective ((j₀ : H₀ →ₐ[R] C).toLinearMap.baseChange K) ∧
      Function.Surjective ((j : H →ₐ[R] C).toLinearMap.baseChange K) ∧
      ∀ y : H₀, (1 : K) ⊗ₜ[R] (j₀ y) =
        ((j : H →ₐ[R] C).toLinearMap.baseChange K) (lam ((1 : K) ⊗ₜ[R] y)) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.solution
