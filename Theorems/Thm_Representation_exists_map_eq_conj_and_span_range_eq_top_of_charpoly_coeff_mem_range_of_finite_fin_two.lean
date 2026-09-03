import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Span.Defs
import P2M.Util
import P2M.Sol.S_Representation_exists_map_eq_conj_and_span_range_eq_top_of_charpoly_coeff_mem_range_of_finite_fin_two
set_option autoImplicit false

theorem Representation.exists_map_eq_conj_and_span_range_eq_top_of_charpoly_coeff_mem_range_of_finite_fin_two
    {G : Type} [Group G] {k₀ : Type} [Field k₀] [Finite k₀] {F : Type} [Field F] (e₀ : k₀ →+* F)
    (ρ : G →* GL (Fin 2) F)
    (hcoeff : ∀ (x : G) (i : ℕ), ((ρ x).val.charpoly).coeff i ∈ e₀.range)
    (habs : ∀ {F' : Type} [Field F'] (e : F →+* F') (u : Fin 2 → F'), u ≠ 0 →
      ∃ x : G, Matrix.mulVec ((ρ x).val.map e) u ∉ F' ∙ u) :
    ∃ (ρ₀ : G →* GL (Fin 2) k₀) (g : GL (Fin 2) F),
      (∀ x : G, (ρ₀ x).val.map e₀ = g.val * (ρ x).val * (g⁻¹).val) ∧
      Submodule.span k₀ (Set.range (fun x : G => (ρ₀ x).val)) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_Representation_exists_map_eq_conj_and_span_range_eq_top_of_charpoly_coeff_mem_range_of_finite_fin_two.solution
