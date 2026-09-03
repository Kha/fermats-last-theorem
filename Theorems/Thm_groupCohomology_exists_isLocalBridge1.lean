import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_LocalBridge
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_isLocalBridge1
set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.exists_isLocalBridge1
    {H : Type} [Group H] {D : Type} [Group D] (π : H →* D)
    {R P B : Rep ℤ D} (f : R ⟶ P) (g : P ⟶ B)
    (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
    {X : Rep ℤ D} {A : Rep ℤ H} (ι : X →+ A) (hι : Function.Injective ι)
    (hιeq : ∀ (h : H) (x : X), ι (X.ρ (π h) x) = A.ρ h (ι x))
    {p : ℕ} {M : Rep (ZMod p) H} (κ : B →+ M →+ A)
    (hκeq : ∀ (h : H) (b : B) (m : M), κ (B.ρ (π h) b) (M.ρ h m) = A.ρ h (κ b m))
    (hκ : ∀ c : B →+ A, ∃! m : M, ∀ b, κ b m = c b)
    (hdiv : ∀ φ : R ⟶ X, ∃ ψ : (ihom (Rep.res π P)).obj A, ∀ x : R, LinearMap.toAddMonoidHom ψ (f.hom x) = ι (φ.hom x)) :
    ∃ Λ : (R ⟶ X) →+ H1 M, IsLocalBridge₁ π f g ι κ Λ := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_isLocalBridge1.solution
