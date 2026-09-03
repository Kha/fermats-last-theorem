import Mathlib
import P2M.Util
import P2M.Sol.S_Module_End_finrank_iInf_eigenspace_baseChange_complex_eq_add

theorem Module.End.finrank_iInf_eigenspace_baseChange_complex_eq_add
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (Λ : Submodule ℤ V) {n : ℕ} (b : Module.Basis (Fin n) ℤ Λ)
    (hli : ∀ r : Fin n → ℝ, ∑ i, ((r i : ℂ)) • ((b i : Λ) : V) = 0 → r = 0)
    (hsp : ∀ v : V, ∃ r : Fin n → ℝ, ∑ i, ((r i : ℂ)) • ((b i : Λ) : V) = v)
    {ι : Type*} (D : ι → Module.End ℂ V) (A : ι → Module.End ℤ Λ)
    (hA : ∀ (i : ι) (x : Λ), ((A i x : Λ) : V) = D i (x : V)) (c : ι → ℂ) :
    Module.finrank ℂ ↥(⨅ i, Module.End.eigenspace ((A i).baseChange ℂ) (c i)) =
      Module.finrank ℂ ↥(⨅ i, Module.End.eigenspace (D i) (c i)) +
        Module.finrank ℂ ↥(⨅ i, Module.End.eigenspace (D i) (starRingEnd ℂ (c i))) := by p2m_exact_reverting @_root_.P2MW.S_Module_End_finrank_iInf_eigenspace_baseChange_complex_eq_add.solution
