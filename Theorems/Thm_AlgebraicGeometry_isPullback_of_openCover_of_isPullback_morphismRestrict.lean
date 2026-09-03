import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isPullback_of_openCover_of_isPullback_morphismRestrict

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
theorem AlgebraicGeometry.isPullback_of_openCover_of_isPullback_morphismRestrict
    {P X Y S : Scheme.{u}} (p : P ⟶ X) (q : P ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S) (w : p ≫ f = q ≫ g)
    (𝒰 : X.OpenCover)
    (h : ∀ i : 𝒰.I₀, IsPullback (p ∣_ (𝒰.f i).opensRange) ((p ⁻¹ᵁ (𝒰.f i).opensRange).ι ≫ q)
      ((𝒰.f i).opensRange.ι ≫ f) g) :
    IsPullback p q f g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isPullback_of_openCover_of_isPullback_morphismRestrict.solution
