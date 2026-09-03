import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_ringKrullDim_localization_tensor_eq_one_of_irreducible

open scoped TensorProduct Polynomial

universe u v

theorem IsIntegrallyClosed.ringKrullDim_localization_tensor_eq_one_of_irreducible
    {Λ A : Type u} [CommRing Λ] [IsDomain Λ] [IsPrincipalIdealRing Λ] {p : Λ} (hp : Irreducible p)
    [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra Λ A] [Algebra Λ[X] A] [IsScalarTower Λ Λ[X] A]
    [Module.Finite Λ[X] A] [FaithfulSMul Λ[X] A]
    (k : Type v) [Field k] [Algebra Λ k] (hk : algebraMap Λ k p = 0)
    (m : Ideal (k ⊗[Λ] A)) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = 1 := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_ringKrullDim_localization_tensor_eq_one_of_irreducible.solution
