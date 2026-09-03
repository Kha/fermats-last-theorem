import Mathlib
import P2M.Util
import P2M.Sol.S_Field_exists_prod_pow_mul_pow_eq_of_root_mem_adjoin_roots

set_option autoImplicit false

theorem Field.exists_prod_pow_mul_pow_eq_of_root_mem_adjoin_roots
    {K L : Type*} [Field K] [Field L] [Algebra K L] (p : ℕ) (hp : p.Prime)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) {n : ℕ}
    (u : Fin n → K) (hu : ∀ i, u i ≠ 0) (β : Fin n → L)
    (hβ : ∀ i, β i ^ p = algebraMap K L (u i))
    (x : K) (hx : x ≠ 0) (γ : L) (hγ : γ ^ p = algebraMap K L x)
    (hmem : γ ∈ IntermediateField.adjoin K (Set.range β)) :
    ∃ (a : Fin n → ℕ) (w : K), x = (∏ i, u i ^ a i) * w ^ p := by p2m_exact_reverting @_root_.P2MW.S_Field_exists_prod_pow_mul_pow_eq_of_root_mem_adjoin_roots.solution
