import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_exists_map_eq_and_existsUnique_hom_of_pullback_of_surjective

set_option autoImplicit false

universe u

theorem MvFormalGroup.exists_map_eq_and_existsUnique_hom_of_pullback_of_surjective
    {B A' A'' A : Type u} [CommRing B] [CommRing A'] [CommRing A''] [CommRing A]
    (p' : B →+* A') (p'' : B →+* A'') (q' : A' →+* A) (q'' : A'' →+* A)
    (hcomm : q'.comp p' = q''.comp p'')
    (hpb : ∀ (a' : A') (a'' : A''), q' a' = q'' a'' → ∃! b : B, p' b = a' ∧ p'' b = a'')
    (n : ℕ) :
    (Function.Surjective q'' → IsLocalHom q'' →
      ∀ (F' : MvFormalGroup n A') (F'' : MvFormalGroup n A'')
        (φ : (F'.map q').Hom (F''.map q'')),
        IsUnit (MvFormalGroup.linearPart φ.toPowerSeries) →
        ∃ (G : MvFormalGroup n B) (Φ : (G.map p'').Hom F'') (Ψ : F''.Hom (G.map p'')),
          G.map p' = F' ∧
          Ψ.comp Φ = MvFormalGroup.Hom.id (G.map p'') ∧
          Φ.comp Ψ = MvFormalGroup.Hom.id F'' ∧
          ∀ i, MvPowerSeries.map q'' (Φ.toPowerSeries i) = φ.toPowerSeries i) ∧
    (∀ (G₁ G₂ : MvFormalGroup n B)
        (α' : (G₁.map p').Hom (G₂.map p')) (α'' : (G₁.map p'').Hom (G₂.map p'')),
        (∀ i, MvPowerSeries.map q' (α'.toPowerSeries i) =
          MvPowerSeries.map q'' (α''.toPowerSeries i)) →
        ∃! α : G₁.Hom G₂,
          (∀ i, MvPowerSeries.map p' (α.toPowerSeries i) = α'.toPowerSeries i) ∧
          (∀ i, MvPowerSeries.map p'' (α.toPowerSeries i) = α''.toPowerSeries i)) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_exists_map_eq_and_existsUnique_hom_of_pullback_of_surjective.solution
