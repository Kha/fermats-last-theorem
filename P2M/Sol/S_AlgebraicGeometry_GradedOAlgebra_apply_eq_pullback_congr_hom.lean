import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_GradedOAlgebra_apply_eq_pullback_congr_hom

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules"
open scoped TensorProduct

theorem solution
    {X X' : Scheme.{u}} (c c' : X' ⟶ X) (h : c = c') (L : X.Modules) (L' : X'.Modules)
    (e : (Scheme.Modules.pullback c).obj L ≅ L')
    {S S' : Type u} [CommRing S] [CommRing S']
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R)
    (R' : Type u) [CommRing R'] [Algebra S' R'] (𝓡' : ℕ → Submodule S' R')
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (ι' : ∀ n : ℕ, 𝓡' n → Γ(L'.tensorPow n, ⊤))
    (ϑ : R →+* R') (hϑdeg : ∀ n, ∀ x ∈ 𝓡 n, ϑ x ∈ 𝓡' n)
    (hϑ : ∀ (n : ℕ) (x : 𝓡 n), ι' n ⟨ϑ x, hϑdeg n x x.2⟩ =
        ((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow n)).app ⊤) (ι n x))) :
    ∀ (n : ℕ) (x : 𝓡 n), ι' n ⟨ϑ x, hϑdeg n x x.2⟩ =
        ((Scheme.Modules.pullbackTensorPowIso c' L n ≪≫ Scheme.Modules.tensorPowMapIso (((Scheme.Modules.pullbackCongr h).app L).symm ≪≫ e) n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction c').unit.app (L.tensorPow n)).app ⊤) (ι n x)) := by
  subst h
  intro n x
  rw [hϑ n x]
  have hI : ((Scheme.Modules.pullbackCongr (rfl : c = c)).app L).symm ≪≫ e = e := by
    ext : 1
    simp [Scheme.Modules.pullbackCongr]
  rw [hI]
