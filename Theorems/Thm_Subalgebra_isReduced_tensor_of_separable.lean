import Mathlib
import P2M.Util
import P2M.Sol.S_Subalgebra_isReduced_tensor_of_separable

open Polynomial
open scoped TensorProduct

universe u

theorem Subalgebra.isReduced_tensor_of_separable
    {Λ K O F₀ : Type u} [CommRing Λ] [IsDomain Λ] [IsPrincipalIdealRing Λ] {p : Λ} (hp : Irreducible p)
    [Field K] [Algebra Λ K] (R A : Subalgebra Λ K) (e : Λ[X] ≃ₐ[Λ] R) (hRA : R ≤ A)
    (hint : ∀ a : A, IsIntegral R (a : K)) [IsNoetherianRing A] (hIC : IsIntegrallyClosed A)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra R O] [Algebra O K] [IsScalarTower R O K] [FaithfulSMul O K]
    (hpO : Irreducible (algebraMap R O (algebraMap Λ R p)))
    (hO : ∀ x : O, ∃ s ∉ Ideal.span {algebraMap Λ R p}, ∃ r : R,
      algebraMap R O r = algebraMap R O s * x)
    {α : K} (hα : IsIntegral O α)
    (hαA : ∃ s ∉ Ideal.span {algebraMap Λ R p}, (s : K) * α ∈ A)
    (hsep : ((minpoly O α).map (Ideal.Quotient.mk
      (Ideal.span {algebraMap R O (algebraMap Λ R p)}))).Separable)
    (hgen : ∀ x : K, ∃ n : ℕ,
      algebraMap O K (algebraMap R O (algebraMap Λ R p)) ^ n * x ∈ Algebra.adjoin O {α})
    [Field F₀] [Algebra Λ F₀] (hs : Function.Surjective (algebraMap Λ F₀))
    (hker : RingHom.ker (algebraMap Λ F₀) = Ideal.span {p})
    (k : Type u) [Field k] [Algebra Λ k] [Algebra F₀ k] [IsScalarTower Λ F₀ k] :
    IsReduced (k ⊗[Λ] A) := by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_isReduced_tensor_of_separable.solution
