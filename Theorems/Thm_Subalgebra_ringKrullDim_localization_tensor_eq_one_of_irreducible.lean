import Mathlib
import P2M.Util
import P2M.Sol.S_Subalgebra_ringKrullDim_localization_tensor_eq_one_of_irreducible

open scoped TensorProduct Polynomial

universe u v

theorem Subalgebra.ringKrullDim_localization_tensor_eq_one_of_irreducible
    {Λ K : Type u} [CommRing Λ] [IsDomain Λ] [IsPrincipalIdealRing Λ] {p : Λ} (hp : Irreducible p)
    [Field K] [Algebra Λ K] (R A : Subalgebra Λ K) (e : Λ[X] ≃ₐ[Λ] R) (hRA : R ≤ A)
    (hint : ∀ a : A, IsIntegral R (a : K))
    (hFT : Algebra.FiniteType Λ A) (hIC : IsIntegrallyClosed A)
    (k : Type v) [Field k] [Algebra Λ k] (hk : algebraMap Λ k p = 0)
    (m : Ideal (k ⊗[Λ] A)) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = 1 := by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_ringKrullDim_localization_tensor_eq_one_of_irreducible.solution
