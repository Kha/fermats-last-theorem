import Mathlib
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_BareDeformation_smoothOfRelativeDimension_of_isRegluingBy

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.BareDeformation.smoothOfRelativeDimension_of_isRegluingBy
    {S : Type} [CommRing S] {Aₛ : Scheme.{0}} {fₛ : Aₛ ⟶ Spec (CommRingCat.of S)} {Lₛ : RelativeGroupLaw S fₛ}
    {B : Type} [CommRing B] [Algebra B S]
    (D₀ : BareDeformation fₛ Lₛ B) (𝒰 : D₀.A.OrderedAffineCover)
    (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (D : BareDeformation fₛ Lₛ B) (hD : D₀.IsRegluingBy 𝒰 τ D)
    (n : ℕ) [SmoothOfRelativeDimension n D₀.f] :
    SmoothOfRelativeDimension n D.f := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_BareDeformation_smoothOfRelativeDimension_of_isRegluingBy.solution
