import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isPullback_homOfLE_morphismRestrict_comp_openCover_lift

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
theorem AlgebraicGeometry.exists_isPullback_homOfLE_morphismRestrict_comp_openCover_lift
    {A₀ Ak Y : Scheme.{u}} (U : A₀.Opens) (g : (U : Scheme.{u}) ⟶ Y)
    (O : A₀.Opens → Y.Opens) (hO : ∀ W : A₀.Opens, g ⁻¹ᵁ O W = U.ι ⁻¹ᵁ W)
    (i₀ : Ak ⟶ A₀) (W : A₀.Opens) (hW : W ≤ U) :
    ∃ aW : (↑(i₀ ⁻¹ᵁ W) : Scheme.{u}) ⟶ ↑(O W),
      aW ≫ (O W).ι = Ak.homOfLE (i₀.preimage_mono hW) ≫ (i₀ ∣_ U) ≫ g ∧
      IsPullback (Ak.homOfLE (i₀.preimage_mono hW)) aW ((i₀ ∣_ U) ≫ g) (O W).ι := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isPullback_homOfLE_morphismRestrict_comp_openCover_lift.solution
