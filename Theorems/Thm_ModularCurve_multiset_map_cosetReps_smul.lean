import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import P2M.Util
import P2M.Sol.S_ModularCurve_multiset_map_cosetReps_smul

theorem ModularCurve.multiset_map_cosetReps_smul (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (α : Type*) (F : UpperHalfPlane → α) (hF : ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : UpperHalfPlane, F (γ • τ) = F τ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) : (Finset.univ.val.map fun i : Fin (ℓ + 1) => F ((Fin.cases (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (fun b : Fin ℓ => ModularGroup.S * ModularGroup.T ^ (b : ℕ)) i : Matrix.SpecialLinearGroup (Fin 2) ℤ) • γ • τ)) = Finset.univ.val.map fun i : Fin (ℓ + 1) => F ((Fin.cases (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (fun b : Fin ℓ => ModularGroup.S * ModularGroup.T ^ (b : ℕ)) i : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_multiset_map_cosetReps_smul.solution
