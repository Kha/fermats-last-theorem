import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_locallyIso_of_locallyIso_pullback_pi_localizationAway

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.locallyIso_of_locallyIso_pullback_pi_localizationAway
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    {X X₁ : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S))
    (f₁ : X₁ ⟶ Spec (CommRingCat.of (∀ i : Fin k, Localization.Away (r i))))
    (c : X₁ ⟶ X) (hc : IsPullback c f₁ f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i : Fin k, Localization.Away (r i))))))
    (L M : X.Modules)
    (h : ∀ s₁ : ↥(Spec (CommRingCat.of (∀ i : Fin k, Localization.Away (r i)))),
      ∃ U₁ : (Spec (CommRingCat.of (∀ i : Fin k, Localization.Away (r i)))).Opens, s₁ ∈ U₁ ∧
        Nonempty ((Scheme.Modules.pullback (f₁ ⁻¹ᵁ U₁).ι).obj ((Scheme.Modules.pullback c).obj L) ≅
          (Scheme.Modules.pullback (f₁ ⁻¹ᵁ U₁).ι).obj ((Scheme.Modules.pullback c).obj M))) :
    ∀ s : ↥(Spec (CommRingCat.of S)), ∃ U : (Spec (CommRingCat.of S)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj L ≅ (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_locallyIso_of_locallyIso_pullback_pi_localizationAway.solution
