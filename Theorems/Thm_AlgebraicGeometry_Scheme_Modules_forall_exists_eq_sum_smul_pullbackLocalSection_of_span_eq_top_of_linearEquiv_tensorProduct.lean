import Mathlib
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_forall_exists_eq_sum_smul_pullbackLocalSection_of_span_eq_top_of_linearEquiv_tensorProduct

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.forall_exists_eq_sum_smul_pullbackLocalSection_of_span_eq_top_of_linearEquiv_tensorProduct
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (M : X.Modules)
    {n : ℕ} (σ : Fin n → Γ(M, ⊤))
    (hσ : letI : Module S Γ(M, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom
      Submodule.span S (Set.range σ) = ⊤)
    (S' : Type u) [CommRing S'] (φ : S →+* S')
    (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of S')) (g : X' ⟶ X)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (hbc : letI : Module S Γ(M, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom
      letI : Module S' Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ ⊤) :=
        Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ (g ⁻¹ᵁ ⊤) le_top).hom
      letI : Algebra S S' := φ.toAlgebra
      ∃ e : S' ⊗[S] Γ(M, ⊤) ≃ₗ[S'] Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ ⊤),
        ∀ (s' : S') (τ : Γ(M, ⊤)), e (s' ⊗ₜ[S] τ) = s' • Scheme.Modules.pullbackLocalSection g τ)
    (t : Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ ⊤)) :
    letI : Module S' Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ ⊤) :=
      Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ (g ⁻¹ᵁ ⊤) le_top).hom
    ∃ c : Fin n → S', t = ∑ i, c i • Scheme.Modules.pullbackLocalSection g (σ i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_forall_exists_eq_sum_smul_pullbackLocalSection_of_span_eq_top_of_linearEquiv_tensorProduct.solution
