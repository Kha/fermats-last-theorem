import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_exists_forall_mem_iff_adjoin_sup_of_linearDisjoint

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.Place.exists_forall_mem_iff_adjoin_sup_of_linearDisjoint
    {k₀ L F : Type} [Field k₀] [Field L] [Field F] [Algebra k₀ L] [Algebra k₀ F] [Algebra L F] [IsScalarTower k₀ L F]
    (F₀ : IntermediateField k₀ F) (K₁ : IntermediateField k₀ L)
    (hgen : IntermediateField.adjoin k₀ (Set.range (algebraMap L F)) ⊔ F₀ = ⊤)
    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → F), (∀ i, a i ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀) →
      LinearIndependent ↥K₁ c → ∑ i, algebraMap L F (c i) * a i = 0 → ∀ i, a i = 0)
    (hdvr : ∀ O : ValuationSubring F, (∀ x : L, algebraMap L F x ∈ O) → O ≠ ⊤ → IsPrincipalIdealRing ↥O)
    (V₁ : ValuationSubring ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀))
    (hK₁V : ∀ (x : ↥K₁) (hx : algebraMap L F (x : L) ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀),
      (⟨algebraMap L F (x : L), hx⟩ : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀)) ∈ V₁)
    (hV₁ : V₁ ≠ ⊤) :
    ∃ P : Place L F, ∀ f : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀), (f : F) ∈ P.toValuationSubring ↔ f ∈ V₁ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_forall_mem_iff_adjoin_sup_of_linearDisjoint.solution
