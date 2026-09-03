import Mathlib
import Definitions.Def_JacJ1Iface
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_comp_openInclusion_eq_openInclusion_comp_of_local_lift

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_comp_openInclusion_eq_openInclusion_comp_of_local_lift
    {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {A₀ X₀ Y Z : Scheme.{u}}
    (U : A₀.Opens) (g : (U : Scheme.{u}) ⟶ Y)
    (O : A₀.Opens → Y.Opens) (hO : ∀ W : A₀.Opens, g ⁻¹ᵁ O W = U.ι ⁻¹ᵁ W)
    (fX₀ : X₀ ⟶ Spec (CommRingCat.of T))
    (V : X₀.Opens) (gZ : (V : Scheme.{u}) ⟶ Z) (qZ : Z ⟶ Spec (CommRingCat.of T'))
    (hgZ : IsPullback gZ (V.ι ≫ fX₀) qZ (Spec.map (CommRingCat.ofHom π)))
    (OX : X₀.Opens → Z.Opens) (hOX : ∀ W : X₀.Opens, gZ ⁻¹ᵁ OX W = V.ι ⁻¹ᵁ W)
    (h₀ : X₀ ⟶ A₀) (hV : V ≤ h₀ ⁻¹ᵁ U)
    (hZ : Z ⟶ Y) (hhZg : gZ ≫ hZ = X₀.homOfLE hV ≫ (h₀ ∣_ U) ≫ g)
    (WX : X₀.Opens) (WA : A₀.Opens) (hWW : WX ≤ h₀ ⁻¹ᵁ WA) :
    ∃ η : (↑(OX WX) : Scheme.{u}) ⟶ ↑(O WA), η ≫ (O WA).ι = (OX WX).ι ≫ hZ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_comp_openInclusion_eq_openInclusion_comp_of_local_lift.solution
