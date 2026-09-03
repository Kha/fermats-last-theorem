import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_map_restrictAlgHom_eq_presheaf_map_of_tmul_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.TwoAffineOpenCover TensorProduct

universe u
theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.map_restrictAlgHom_eq_presheaf_map_of_tmul_eq
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {X Y : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R)) (p : Y ⟶ X) (πA : Y ⟶ Spec (CommRingCat.of A))
    {U U' : X.Opens} (h : U' ≤ U) {W W' : Y.Opens} (hW : W ≤ p ⁻¹ᵁ U) (hW' : W' ≤ p ⁻¹ᵁ U') (hWW : W' ≤ W)
    (σ : letI := algebraOfHom π U
      A ⊗[R] Γ(X, U) →+* Γ(Y, W))
    (σ' : letI := algebraOfHom π U'
      A ⊗[R] Γ(X, U') →+* Γ(Y, W'))
    (hσ₁ : letI := algebraOfHom π U
      ∀ x : Γ(X, U), σ ((1 : A) ⊗ₜ[R] x) = (Y.presheaf.map (homOfLE hW).op).hom ((p.app U).hom x))
    (hσ₂ : letI := algebraOfHom π U
      letI := algebraOfHom πA W
      ∀ a : A, σ (a ⊗ₜ[R] (1 : Γ(X, U))) = algebraMap A Γ(Y, W) a)
    (hσ'₁ : letI := algebraOfHom π U'
      ∀ x : Γ(X, U'), σ' ((1 : A) ⊗ₜ[R] x) = (Y.presheaf.map (homOfLE hW').op).hom ((p.app U').hom x))
    (hσ'₂ : letI := algebraOfHom π U'
      letI := algebraOfHom πA W'
      ∀ a : A, σ' (a ⊗ₜ[R] (1 : Γ(X, U'))) = algebraMap A Γ(Y, W') a) :
    letI := algebraOfHom π U
    letI := algebraOfHom π U'
    ∀ y : A ⊗[R] Γ(X, U),
      σ' (Algebra.TensorProduct.map (AlgHom.id A A) (restrictAlgHom π h) y) = (Y.presheaf.map (homOfLE hWW).op).hom (σ y) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_map_restrictAlgHom_eq_presheaf_map_of_tmul_eq.solution
