import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import P2M.Util
import P2M.Sol.S_ModularCurve_DRLevel_exists_comp_pair_fibre_of_ringHom

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel IsLocalRing

theorem ModularCurve.DRLevel.exists_comp_pair_fibre_of_ringHom
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]
    (w : DRLevel.X N₀ q ≅ DRLevel.X N₀ q) (hw : w.hom ≫ DRLevel.toBase N₀ q = DRLevel.toBase N₀ q)
    (π : SchemeHomOver (DRLevel.toBase N₀ q) (DRLevel.toBase0 N₀ q))
    (κ₀ : Type) [Field κ₀] (toκ₀ : DRLevel.R q →+* κ₀)
    (comp₀ : Fin 2 → (DRLevel.fibre0 (N₀ := N₀) toκ₀ ⟶ DRLevel.fibre (N₀ := N₀) toκ₀))
    (hover : ∀ i, comp₀ i ≫ pullback.snd _ _ = pullback.snd _ _)
    (hci : ∀ i, IsClosedImmersion (comp₀ i))
    (hsurj : ∀ y : DRLevel.fibre (N₀ := N₀) toκ₀, y ∈ Set.range (comp₀ 0).base ∨ y ∈ Set.range (comp₀ 1).base)
    (hne : Set.range (comp₀ 0).base ≠ Set.range (comp₀ 1).base)
    (hpi : comp₀ 0 ≫ DRLevel.fibreMap0 π toκ₀ = 𝟙 _)
    (hcw : comp₀ 0 ≫ DRLevel.fibreMap w.hom hw toκ₀ = comp₀ 1)
    (κ : Type) [Field κ] (toκ : DRLevel.R q →+* κ) (φ : κ₀ →+* κ) (hφ : φ.comp toκ₀ = toκ) :
    ∃ comp : Fin 2 → (DRLevel.fibre0 (N₀ := N₀) toκ ⟶ DRLevel.fibre (N₀ := N₀) toκ),
      (∀ i, comp i ≫ pullback.snd _ _ = pullback.snd _ _) ∧
      (∀ i, IsClosedImmersion (comp i)) ∧
      (∀ y : DRLevel.fibre (N₀ := N₀) toκ, y ∈ Set.range (comp 0).base ∨ y ∈ Set.range (comp 1).base) ∧
      Set.range (comp 0).base ≠ Set.range (comp 1).base ∧
      comp 0 ≫ DRLevel.fibreMap0 π toκ = 𝟙 _ ∧
      comp 0 ≫ DRLevel.fibreMap w.hom hw toκ = comp 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRLevel_exists_comp_pair_fibre_of_ringHom.solution
