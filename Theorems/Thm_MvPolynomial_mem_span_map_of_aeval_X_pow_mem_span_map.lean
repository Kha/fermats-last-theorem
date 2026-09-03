import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_mem_span_map_of_aeval_X_pow_mem_span_map

set_option autoImplicit false

theorem MvPolynomial.mem_span_map_of_aeval_X_pow_mem_span_map
    {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [Algebra (ZMod p) K] {σ : Type*} (n : ℕ)
    (f : MvPolynomial σ (ZMod p)) (hf : Prime f) (g : MvPolynomial σ K)
    (hg : MvPolynomial.aeval (fun i => (MvPolynomial.X i : MvPolynomial σ K) ^ p ^ n) g ∈
      Ideal.span {MvPolynomial.map (algebraMap (ZMod p) K) f}) :
    g ∈ Ideal.span {MvPolynomial.map (algebraMap (ZMod p) K) f} := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_mem_span_map_of_aeval_X_pow_mem_span_map.solution
