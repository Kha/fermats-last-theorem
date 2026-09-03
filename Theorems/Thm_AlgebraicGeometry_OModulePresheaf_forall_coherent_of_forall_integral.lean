import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_forall_coherent_of_forall_integral

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.OModulePresheaf.forall_coherent_of_forall_integral
    {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsProper π]
    (Q : Closeds V → OModulePresheaf π → Prop)
    (h0 : ∀ (Y : Closeds V) (G : OModulePresheaf π), (∀ U : V.affineOpens, Subsingleton (G.obj U.1)) → Q Y G)
    (hmono : ∀ (Y Y' : Closeds V) (G : OModulePresheaf π), Y' ≤ Y → Q Y' G → Q Y G)
    (hext : ∀ (Y : Closeds V) (G₁ G₂ G₃ : OModulePresheaf π), Nonempty (OModulePresheaf.AffSES G₁ G₂ G₃) →
      G₁.IsCoherent → G₁.IsQuasicoherent → G₂.IsCoherent → G₂.IsQuasicoherent →
      G₃.IsCoherent → G₃.IsQuasicoherent →
      (Q Y G₁ → Q Y G₃ → Q Y G₂) ∧ (Q Y G₁ → Q Y G₂ → Q Y G₃) ∧ (Q Y G₂ → Q Y G₃ → Q Y G₁))
    (hInt : ∀ Z₀ : Closeds V, (Z₀ : Set V).Nonempty →
      IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme →
      (∀ Y' < Z₀, ∀ G : OModulePresheaf π, G.IsCoherent → G.IsQuasicoherent → G.SupportedIn Y' → Q Y' G) →
      Q Z₀ (OModulePresheaf.pushforwardUnit π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι)) :
    ∀ (Y : Closeds V) (F : OModulePresheaf π), F.IsCoherent → F.IsQuasicoherent → F.SupportedIn Y → Q Y F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_coherent_of_forall_integral.solution
