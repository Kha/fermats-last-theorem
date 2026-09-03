import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_card_le_of_subset_support

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.card_le_of_subset_support
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ} {k : Type u} [Field k] {x : Spec (CommRingCat.of k) ⟶ S}
    (D : RelEffCartierDiv f r x) (F : Finset ↥(pullback f x)) (hF : ∀ z ∈ F, z ∈ D.I.support) :
    F.card ≤ r := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelEffCartierDiv_card_le_of_subset_support.solution
