import Mathlib
import P2M.Util
import P2M.Sol.S_Submodule_span_fixedPoints_eq_top_of_frobenius_semilinear_injective

set_option autoImplicit false

theorem Submodule.span_fixedPoints_eq_top_of_frobenius_semilinear_injective
    {K V : Type*} [Field K] [IsAlgClosed K] {p : ℕ} [Fact p.Prime] [CharP K p]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (s : ℕ) (hs : s ≠ 0) (θ : V →+ V)
    (hθ : ∀ (c : K) (v : V), θ (c • v) = c ^ p ^ s • θ v) (hinj : Function.Injective θ) :
    Submodule.span K (Function.fixedPoints θ) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_Submodule_span_fixedPoints_eq_top_of_frobenius_semilinear_injective.solution
