import Mathlib
import P2M.Util
import P2M.Sol.S_IsGaloisGroup_exists_subalgebra_fixedPoints_inertia_etale_and_isLocalRing_and_finrank_eq

set_option autoImplicit false

open scoped Pointwise

theorem IsGaloisGroup.exists_subalgebra_fixedPoints_inertia_etale_and_isLocalRing_and_finrank_eq
    {A B : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [IsIntegrallyClosed A]
    [CommRing B] [IsDomain B] [IsLocalRing B]
    [Algebra A B] [Module.Finite A B] [FaithfulSMul A B] [IsLocalHom (algebraMap A B)]
    (D : Type*) [Group D] [Finite D] [MulSemiringAction D B] [IsGaloisGroup D A B]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)] :
    ∃ B₁ : Subalgebra A B,
      (∀ b : B, b ∈ B₁ ↔ ∀ d ∈ (IsLocalRing.maximalIdeal B).inertia D, d • b = b) ∧
      IsGaloisGroup ↥((IsLocalRing.maximalIdeal B).inertia D) ↥B₁ B ∧
      Algebra.Etale A ↥B₁ ∧ IsLocalRing ↥B₁ ∧
      Function.Surjective (fun b₁ : ↥B₁ => IsLocalRing.residue B (b₁ : B)) ∧
      Module.Free A ↥B₁ ∧
      Module.finrank A ↥B₁ =
        Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) ∧
      ((IsLocalRing.maximalIdeal B).inertia D).index =
        Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) := by p2m_exact_reverting @_root_.P2MW.S_IsGaloisGroup_exists_subalgebra_fixedPoints_inertia_etale_and_isLocalRing_and_finrank_eq.solution
