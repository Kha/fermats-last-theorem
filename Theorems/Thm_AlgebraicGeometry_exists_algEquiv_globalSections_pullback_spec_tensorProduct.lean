import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_algEquiv_globalSections_pullback_spec_tensorProduct
set_option Elab.async false
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.exists_algEquiv_globalSections_pullback_spec_tensorProduct
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsAffine X]
    (S : Type u) [CommRing S] [Algebra R S] :
    letI : Algebra R Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom.toAlgebra
    letI : Algebra S Γ(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R S))), ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop).hom.toAlgebra
    ∃ e : S ⊗[R] Γ(X, ⊤) ≃ₐ[S] Γ(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R S))), ⊤),
      ∀ a : Γ(X, ⊤), e (1 ⊗ₜ a) =
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop a := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_algEquiv_globalSections_pullback_spec_tensorProduct.solution
