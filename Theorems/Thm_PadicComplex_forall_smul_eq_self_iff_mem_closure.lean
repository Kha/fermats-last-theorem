import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import P2M.Util
import P2M.Sol.S_PadicComplex_forall_smul_eq_self_iff_mem_closure

set_option autoImplicit false

theorem PadicComplex.forall_smul_eq_self_iff_mem_closure
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (x : ℂ_[p]) :
    (∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ K.fixingSubgroup → σ • x = x) ↔
      x ∈ closure (Set.range fun k : K => ((k : PadicAlgCl p) : ℂ_[p])) := by p2m_exact_reverting @_root_.P2MW.S_PadicComplex_forall_smul_eq_self_iff_mem_closure.solution
