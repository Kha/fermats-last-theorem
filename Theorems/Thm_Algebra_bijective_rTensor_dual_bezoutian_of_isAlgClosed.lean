import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_bijective_rTensor_dual_bezoutian_of_isAlgClosed

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.bijective_rTensor_dual_bezoutian_of_isAlgClosed
    (K : Type*) [Field K] [IsAlgClosed K] {m : ℕ} (g : Fin m → MvPolynomial (Fin m) K)
    [Module.Finite K (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g))]
    (b : Fin m → Fin m → MvPolynomial (Fin m) K ⊗[K] MvPolynomial (Fin m) K)
    (hb : ∀ i, g i ⊗ₜ[K] (1 : MvPolynomial (Fin m) K) - (1 : MvPolynomial (Fin m) K) ⊗ₜ[K] g i =
      ∑ j, b i j * (MvPolynomial.X j ⊗ₜ[K] 1 - 1 ⊗ₜ[K] MvPolynomial.X j)) :
    Function.Bijective (fun φ : Module.Dual K (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g)) =>
      TensorProduct.lid K (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g))
        (LinearMap.rTensor (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g)) φ
          (Algebra.TensorProduct.map
              (Ideal.Quotient.mkₐ K (Ideal.span (Set.range g))) (Ideal.Quotient.mkₐ K (Ideal.span (Set.range g)))
            (Matrix.det (Matrix.of b))))) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_bijective_rTensor_dual_bezoutian_of_isAlgClosed.solution
