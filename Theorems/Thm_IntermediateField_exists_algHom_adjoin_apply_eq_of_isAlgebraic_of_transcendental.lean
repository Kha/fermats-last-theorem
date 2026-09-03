import Mathlib
import P2M.Util
import P2M.Sol.S_IntermediateField_exists_algHom_adjoin_apply_eq_of_isAlgebraic_of_transcendental

theorem IntermediateField.exists_algHom_adjoin_apply_eq_of_isAlgebraic_of_transcendental
    (K : Type*) {L L' : Type*} [Field K] [Field L] [Algebra K L] [Field L'] [Algebra K L']
    (G : Set L) (h1 : (1 : L) ∈ G) (hmul : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G)
    (θ : L → L') (hθ : ∀ x ∈ G, ∀ y ∈ G, θ (x * y) = θ x * θ y)
    (hlin : ∀ c : L →₀ K, (↑c.support : Set L) ⊆ G →
      (c.sum fun x r => r • x) = 0 → (c.sum fun x r => r • θ x) = 0)
    (F : IntermediateField K L) (hF : F = IntermediateField.adjoin K G)
    (x₀ : F) (hx₀G : (x₀ : L) ∈ G) (hx₀ : Transcendental K (θ x₀))
    (halg : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x₀} : Set F)) F) :
    ∃ Θ : F →ₐ[K] L', ∀ x : F, (x : L) ∈ G → Θ x = θ x := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_exists_algHom_adjoin_apply_eq_of_isAlgebraic_of_transcendental.solution
