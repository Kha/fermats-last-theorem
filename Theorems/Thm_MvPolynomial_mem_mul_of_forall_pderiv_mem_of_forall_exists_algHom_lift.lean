import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_mem_mul_of_forall_pderiv_mem_of_forall_exists_algHom_lift

set_option autoImplicit false

open MvPolynomial

theorem MvPolynomial.mem_mul_of_forall_pderiv_mem_of_forall_exists_algHom_lift
    (R : Type) [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (I J : Ideal (MvPolynomial (Fin n) R)) (hIJ : I ≤ J) (hJ : J.IsMaximal)

    (D : ℕ → Type) [∀ N, CommRing (D N)] [∀ N, Algebra R (D N)]
    [∀ N, Algebra (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N)]
    [∀ N, IsScalarTower R (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N)]
    [∀ N, Module.FaithfullyFlat (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N)]
    (σ : ∀ N, (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] D N)
    (hσ : ∀ (N : ℕ) (f : MvPolynomial (Fin n) R),
      σ N (Ideal.Quotient.mk I f) -
          algebraMap (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N) (Ideal.Quotient.mk (J ^ N ⊔ J * I) f) ∈
        Ideal.map (algebraMap (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N))
          (Ideal.map (Ideal.Quotient.mk (J ^ N ⊔ J * I)) (J ^ N ⊔ I)))
    (v : MvPolynomial (Fin n) R) (hv : v ∈ I) (hdv : ∀ i : Fin n, MvPolynomial.pderiv i v ∈ J) :
    v ∈ J * I := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_mem_mul_of_forall_pderiv_mem_of_forall_exists_algHom_lift.solution
