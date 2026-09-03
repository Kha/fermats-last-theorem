import Definitions.Def_AutomorphicForm_CuspidalConstituent
import P2M.Util
import P2M.Sol.S_AutomorphicForm_CuspidalConstituent_eq_of_isCuspConstituent_of_exists_mem_ne_zero

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.CuspidalConstituent.eq_of_isCuspConstituent_of_exists_mem_ne_zero
    (F : Type) [Field F] [NumberField F] (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (V₁ V₂ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (h₁ : AutomorphicForm.CuspidalConstituent.IsCuspConstituent F pins ξ V₁)
    (h₂ : AutomorphicForm.CuspidalConstituent.IsCuspConstituent F pins ξ V₂)
    (h : ∃ φ ∈ V₁ ⊓ V₂, φ ≠ 0) : V₁ = V₂ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_CuspidalConstituent_eq_of_isCuspConstituent_of_exists_mem_ne_zero.solution
