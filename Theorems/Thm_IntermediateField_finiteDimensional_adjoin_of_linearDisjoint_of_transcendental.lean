import Mathlib
import P2M.Util
import P2M.Sol.S_IntermediateField_finiteDimensional_adjoin_of_linearDisjoint_of_transcendental

set_option autoImplicit false

theorem IntermediateField.finiteDimensional_adjoin_of_linearDisjoint_of_transcendental
    {K₀ L F₀ F : Type*} [Field K₀] [Field L] [Field F₀] [Field F]
    [Algebra K₀ F₀] [Algebra L F] [Algebra F₀ F]
    (hld : ∀ (n : ℕ) (b : Fin n → F₀), LinearIndependent K₀ b →
      LinearIndependent L (fun i => algebraMap F₀ F (b i)))
    (x : F₀) (hx : Transcendental K₀ x)
    [FiniteDimensional (IntermediateField.adjoin L ({algebraMap F₀ F x} : Set F)) F] :
    FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set F₀)) F₀ := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_finiteDimensional_adjoin_of_linearDisjoint_of_transcendental.solution
