import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_tensorProduct_sections_pullback_of_forall_isPullback_of_iso

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.exists_linearEquiv_tensorProduct_sections_pullback_of_forall_isPullback_of_iso
    {S₀ : Type u} [CommRing S₀] {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of S₀)) (𝓛₀ : A₀.Modules)
    (hbc₀ : ∀ (B : Type u) [CommRing B] (ψ : S₀ →+* B)
      (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of B)) (g : X' ⟶ A₀),
      IsPullback g f' f₀ (Spec.map (CommRingCat.ofHom ψ)) →
      letI : Module S₀ Γ(𝓛₀, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S₀)).inv ≫ f₀.appTop).hom
      letI : Module B Γ((Scheme.Modules.pullback g).obj 𝓛₀, g ⁻¹ᵁ ⊤) :=
        Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ f'.appLE ⊤ (g ⁻¹ᵁ ⊤) le_top).hom
      letI : Algebra S₀ B := ψ.toAlgebra
      ∃ e : B ⊗[S₀] Γ(𝓛₀, ⊤) ≃ₗ[B] Γ((Scheme.Modules.pullback g).obj 𝓛₀, g ⁻¹ᵁ ⊤),
        ∀ (b : B) (m : Γ(𝓛₀, ⊤)), e (b ⊗ₜ[S₀] m) = b • Scheme.Modules.pullbackLocalSection g m)
    {S : Type u} [CommRing S] (ψ₀ : S₀ →+* S) {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (g₀ : A ⟶ A₀)
    (hg₀ : IsPullback g₀ f f₀ (Spec.map (CommRingCat.ofHom ψ₀)))
    (𝓛 : A.Modules) (e₀ : (Scheme.Modules.pullback g₀).obj 𝓛₀ ≅ 𝓛)
    (S' : Type u) [CommRing S'] (φ : S →+* S')
    (A' : Scheme.{u}) (f' : A' ⟶ Spec (CommRingCat.of S')) (gA : A' ⟶ A)
    (hg : IsPullback gA f' f (Spec.map (CommRingCat.ofHom φ))) :
    letI : Module S Γ(𝓛, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom
    letI : Module S' Γ((Scheme.Modules.pullback gA).obj 𝓛, gA ⁻¹ᵁ ⊤) :=
      Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ (gA ⁻¹ᵁ ⊤) le_top).hom
    letI : Algebra S S' := φ.toAlgebra
    ∃ e : S' ⊗[S] Γ(𝓛, ⊤) ≃ₗ[S'] Γ((Scheme.Modules.pullback gA).obj 𝓛, gA ⁻¹ᵁ ⊤),
      ∀ (b : S') (m : Γ(𝓛, ⊤)), e (b ⊗ₜ[S] m) = b • Scheme.Modules.pullbackLocalSection gA m := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_tensorProduct_sections_pullback_of_forall_isPullback_of_iso.solution
