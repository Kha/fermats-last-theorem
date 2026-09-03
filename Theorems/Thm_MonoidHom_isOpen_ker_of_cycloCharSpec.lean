import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import P2M.Util
import P2M.Sol.S_MonoidHom_isOpen_ker_of_cycloCharSpec

set_option autoImplicit false

theorem MonoidHom.isOpen_ker_of_cycloCharSpec (m : ℕ) [NeZero m]
    (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod m)ˣ)
    (hcyc : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ),
      μ ^ m = 1 → σ μ = μ ^ ((cyc σ : ZMod m)).val) :
    IsOpen ((cyc.ker : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
      Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) := by p2m_exact_reverting @_root_.P2MW.S_MonoidHom_isOpen_ker_of_cycloCharSpec.solution
