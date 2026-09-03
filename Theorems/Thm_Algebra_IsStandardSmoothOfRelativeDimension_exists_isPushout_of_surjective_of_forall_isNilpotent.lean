import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_IsStandardSmoothOfRelativeDimension_exists_isPushout_of_surjective_of_forall_isNilpotent

set_option autoImplicit false

universe u

theorem Algebra.IsStandardSmoothOfRelativeDimension.exists_isPushout_of_surjective_of_forall_isNilpotent
    (n : ℕ) {R R₀ : Type u} [CommRing R] [CommRing R₀] [Algebra R R₀]
    (hf : Function.Surjective (algebraMap R R₀))
    (hnil : ∀ x ∈ RingHom.ker (algebraMap R R₀), IsNilpotent x)
    (A₀ : Type u) [CommRing A₀] [Algebra R₀ A₀] [Algebra R A₀] [IsScalarTower R R₀ A₀]
    [Algebra.IsStandardSmoothOfRelativeDimension n R₀ A₀] :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra A A₀) (_ : IsScalarTower R A A₀),
      Algebra.IsStandardSmoothOfRelativeDimension n R A ∧
      Function.Surjective (algebraMap A A₀) ∧
      RingHom.ker (algebraMap A A₀) = Ideal.map (algebraMap R A) (RingHom.ker (algebraMap R R₀)) ∧
      Algebra.IsPushout R R₀ A A₀ := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsStandardSmoothOfRelativeDimension_exists_isPushout_of_surjective_of_forall_isNilpotent.solution
