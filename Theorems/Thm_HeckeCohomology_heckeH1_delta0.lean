import Definitions.Def_GroupCohomology_TransferHecke
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import P2M.Util
import P2M.Sol.S_HeckeCohomology_heckeH1_delta0

set_option autoImplicit false
open CategoryTheory groupCohomology in

theorem HeckeCohomology.heckeH1_delta0 {k Γ : Type} [CommRing k] [Group Γ]
    (S₁ S₂ : Subgroup Γ) (c : S₂ →* S₁) [S₂.FiniteIndex]
    {X : ShortComplex (Rep k Γ)} (hX : X.ShortExact)
    (φ₁ : X.X₁ →ₗ[k] X.X₁) (hφ₁ : IsTwist S₁ S₂ c X.X₁ φ₁)
    (φ₂ : X.X₂ →ₗ[k] X.X₂) (hφ₂ : IsTwist S₁ S₂ c X.X₂ φ₂)
    (φ₃ : X.X₃ →ₗ[k] X.X₃) (hφ₃ : IsTwist S₁ S₂ c X.X₃ φ₃)
    (hf : ∀ a : X.X₁, X.f.hom (φ₁ a) = φ₂ (X.f.hom a))
    (hg : ∀ b : X.X₂, X.g.hom (φ₂ b) = φ₃ (X.g.hom b))
    (z : X.X₃.ρ.invariants) :
    heckeH1 S₁ S₂ c X.X₁ φ₁ hφ₁ (δ hX 0 1 rfl ((H0Iso X.X₃).inv z)) =
      δ hX 0 1 rfl ((H0Iso X.X₃).inv (heckeInv S₁ S₂ c X.X₃ φ₃ hφ₃ z)) := by p2m_exact_reverting @_root_.P2MW.S_HeckeCohomology_heckeH1_delta0.solution
