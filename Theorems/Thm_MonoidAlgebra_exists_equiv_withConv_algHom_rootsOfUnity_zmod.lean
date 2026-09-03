import Mathlib
import P2M.Util
import P2M.Sol.S_MonoidAlgebra_exists_equiv_withConv_algHom_rootsOfUnity_zmod

theorem MonoidAlgebra.exists_equiv_withConv_algHom_rootsOfUnity_zmod
    (K : Type) [Field K] [CharZero K] (n : ℕ) [NeZero n] :
    ∃ eμ : WithConv (MonoidAlgebra K (Multiplicative (ZMod n)) →ₐ[K] AlgebraicClosure K)
        ≃ rootsOfUnity n (AlgebraicClosure K),
      (∀ f g, eμ (f * g) = eμ f * eμ g) ∧
      ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) f g,
        (∀ a, g a = σ (f a))
        → ((eμ g : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
          = σ ((eμ f : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) := by p2m_exact_reverting @_root_.P2MW.S_MonoidAlgebra_exists_equiv_withConv_algHom_rootsOfUnity_zmod.solution
