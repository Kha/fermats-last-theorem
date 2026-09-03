import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_BilinForm_sup_iSup_range_ne_top_of_orthogonal_le_of_finrank_ker_aeval_eq_two_mul

set_option autoImplicit false

theorem LinearMap.BilinForm.sup_iSup_range_ne_top_of_orthogonal_le_of_finrank_ker_aeval_eq_two_mul
    {K V R : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [CommRing R] [Algebra K R] (φ : R →ₐ[K] Module.End K V)
    (B : LinearMap.BilinForm K V)
    (hBl : ∀ v : V, (∀ w : V, B v w = 0) → v = 0) (hBr : ∀ w : V, (∀ v : V, B v w = 0) → w = 0)
    (hadj : ∀ (r : R) (v w : V), B (φ r v) w = B v (φ r w))
    (V₀ : Submodule K V) (hst : ∀ (r : R), ∀ v ∈ V₀, φ r v ∈ V₀)
    (hco : ∀ w : V, (∀ v ∈ V₀, B v w = 0) → w ∈ V₀)
    (t : R) (Pu Pn : Polynomial K) (hcop : IsCoprime Pu Pn)
    (hann : Polynomial.aeval (φ t) (Pu * Pn) = 0)
    (hn : LinearMap.ker (Polynomial.aeval (φ t) Pn) ≤ V₀)
    (hu : Module.finrank K ↥(LinearMap.ker (Polynomial.aeval (φ t) Pu)) =
      2 * (Module.finrank K V - Module.finrank K V₀))
    (𝔪 : Ideal R) (h𝔪 : 𝔪 ≠ ⊤) (hker : ∀ r : R, φ r = 0 → r ∈ 𝔪)
    (c : K) (htc : t - algebraMap K R c ∈ 𝔪) (hc : Pn.eval c ≠ 0) :
    V₀ ⊔ (⨆ r ∈ 𝔪, LinearMap.range (φ r)) ≠ ⊤ := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_BilinForm_sup_iSup_range_ne_top_of_orthogonal_le_of_finrank_ker_aeval_eq_two_mul.solution
