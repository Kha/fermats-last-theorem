import Definitions.Def_ModularCurve_ShimuraCovering
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_AlgebraicCurve_Correspondence
import Mathlib.FieldTheory.Galois.Basic
import P2M.Util
import P2M.Sol.S_ModularCurve_laurentBaseChange_deck_galois_package
set_option autoImplicit false
open ModularCurve AlgebraicCurve
theorem ModularCurve.laurentBaseChange_deck_galois_package
    (L : Type*) [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L]
    {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (h : F₀ ≤ F₁)
    {Γ : Type*} [Group Γ] [Finite Γ] (δ : Γ →* (F₁ ≃ₐ[ℚ] F₁))
    (hfix : ∀ (g : Γ) (x : F₁), (x : LaurentSeries ℚ) ∈ F₀ → δ g x = x)
    (hgal : ∀ x : F₁, (∀ g : Γ, δ g x = x) → (x : LaurentSeries ℚ) ∈ F₀) :
    (inclusionBar L h).fieldRange
        = IntermediateField.fixedField ((geomAut L F₁).comp δ).range ∧
      FiniteAlong L (inclusionBar L h) ∧
      finrankAlong L (inclusionBar L h) = Nat.card ((geomAut L F₁).comp δ).range := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_laurentBaseChange_deck_galois_package.solution
