import Mathlib
import P2M.Util
import P2M.Sol.S_Module_End_exists_monic_map_eq_charpoly_and_charpoly_eq_sq_of_span_real_dual_eq_top

set_option autoImplicit false

theorem Module.End.exists_monic_map_eq_charpoly_and_charpoly_eq_sq_of_span_real_dual_eq_top
    {S : Type*} [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
    (T : S →ₗ[ℂ] S) (hreal : T.charpoly.map (starRingEnd ℂ) = T.charpoly)
    (Λ : Submodule ℤ (Module.Dual ℂ S)) [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    {n : ℕ} (b : Module.Basis (Fin n) ℤ Λ)
    (hli : LinearIndependent ℝ (fun i => ((b i : Λ) : Module.Dual ℂ S)))
    (hsp : Submodule.span ℝ (Set.range fun i => ((b i : Λ) : Module.Dual ℂ S)) = ⊤)
    (τ : Module.End ℤ Λ)
    (hτ : ∀ x : Λ, ((τ x : Λ) : Module.Dual ℂ S) = (x : Module.Dual ℂ S) ∘ₗ T) :
    ∃ Q : Polynomial ℤ, Q.Monic ∧ Q.map (algebraMap ℤ ℂ) = T.charpoly ∧ τ.charpoly = Q ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_Module_End_exists_monic_map_eq_charpoly_and_charpoly_eq_sq_of_span_real_dual_eq_top.solution
