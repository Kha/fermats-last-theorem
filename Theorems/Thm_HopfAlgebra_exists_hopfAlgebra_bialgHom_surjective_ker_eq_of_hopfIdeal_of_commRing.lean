import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal_of_commRing
set_option autoImplicit false
universe u v
open scoped TensorProduct

theorem HopfAlgebra.exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal_of_commRing
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A] (I : Ideal A)
    (hcomul : ∀ a ∈ I, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
      (Coalgebra.comul (R := R) a) = 0)
    (hcounit : ∀ a ∈ I, Coalgebra.counit (R := R) a = 0)
    (hanti : ∀ a ∈ I, HopfAlgebraStruct.antipode (R := R) a ∈ I) :
    ∃ (A' : Type v) (_ : CommRing A') (_ : HopfAlgebra R A') (π : A →ₐc[R] A'),
      Function.Surjective π ∧
      RingHom.ker (π : A →+* A') = I ∧
      (Coalgebra.IsCocomm R A → Coalgebra.IsCocomm R A') ∧
      (Module.Finite R A → Module.Finite R A') ∧
      (∀ (T : Type v) [CommRing T] [Algebra R T] (φ : A →ₐ[R] T),
        I ≤ RingHom.ker (φ : A →+* T) → ∃! φ' : A' →ₐ[R] T, φ'.comp (π : A →ₐ[R] A') = φ) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal_of_commRing.solution
