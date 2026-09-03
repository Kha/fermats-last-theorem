import Mathlib
import P2M.Util
import P2M.Sol.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent

set_option autoImplicit false

universe u v

theorem IntermediateField.mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent
    {k : Type u} {K : Type v} [Field k] [Infinite k] [Field K] [Algebra k K]
    (hfg : (⊤ : IntermediateField k K).FG)
    (hsc : ∀ θ : K, IsSeparable k θ → θ ∈ (⊥ : IntermediateField k K))
    {n : ℕ} (g : Fin (n + 1) → K) (c : Fin (n + 1) → k)
    (x : Fin (n + 1) → FractionRing (MvPolynomial (Fin (n + 1)) K))
    (hx : ∀ i, x i = algebraMap (MvPolynomial (Fin (n + 1)) K) _ (MvPolynomial.X i))
    (hind : AlgebraicIndependent k
      (Fin.snoc (Fin.snoc x (∑ i, algebraMap K _ (g i) * x i)) (algebraMap K _ (∑ i, c i • g i))))
    (θ : FractionRing (MvPolynomial (Fin (n + 1)) K))
    (hθ : IsSeparable
      (IntermediateField.adjoin k (Set.range x ∪ {∑ i, algebraMap K _ (g i) * x i})) θ) :
    θ ∈ IntermediateField.adjoin k (Set.range x ∪ {∑ i, algebraMap K _ (g i) * x i}) := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.solution
