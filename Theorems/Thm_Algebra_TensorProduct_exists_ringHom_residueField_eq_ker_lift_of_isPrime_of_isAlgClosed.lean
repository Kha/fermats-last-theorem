import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_TensorProduct_exists_ringHom_residueField_eq_ker_lift_of_isPrime_of_isAlgClosed

set_option autoImplicit false

open IsLocalRing TensorProduct

theorem Algebra.TensorProduct.exists_ringHom_residueField_eq_ker_lift_of_isPrime_of_isAlgClosed
    (A₀ A : Type) [CommRing A₀] [IsLocalRing A₀] [CommRing A] [IsLocalRing A] [Algebra A₀ A]
    [IsLocalHom (algebraMap A₀ A)] [IsAlgClosed (ResidueField A)]
    (B₀ : Type) [CommRing B₀] [Algebra A₀ B₀] [Algebra.FiniteType A₀ B₀]
    (𝔪₀ : Ideal B₀) [𝔪₀.IsMaximal] (h𝔪₀ : ∀ a ∈ maximalIdeal A₀, algebraMap A₀ B₀ a ∈ 𝔪₀)
    (P : Ideal (A ⊗[A₀] B₀)) [P.IsPrime]
    (hP₀ : ∀ b ∈ 𝔪₀, (1 : A) ⊗ₜ[A₀] b ∈ P)
    (hPA : ∀ a ∈ maximalIdeal A, a ⊗ₜ[A₀] (1 : B₀) ∈ P) :
    ∃ (χ : B₀ →+* ResidueField A)
      (hχA₀ : ∀ a : A₀, χ (algebraMap A₀ B₀ a) = IsLocalRing.residue A (algebraMap A₀ A a)),
      let ev : A ⊗[A₀] B₀ →+* ResidueField A :=
        (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom A₀ A (ResidueField A))
          ({ toRingHom := χ, commutes' := fun a => by
              rw [IsScalarTower.algebraMap_apply A₀ A (ResidueField A)]; exact hχA₀ a } : B₀ →ₐ[A₀] ResidueField A)
          (fun _ _ => Commute.all _ _)).toRingHom
      P = RingHom.ker ev := by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_exists_ringHom_residueField_eq_ker_lift_of_isPrime_of_isAlgClosed.solution
