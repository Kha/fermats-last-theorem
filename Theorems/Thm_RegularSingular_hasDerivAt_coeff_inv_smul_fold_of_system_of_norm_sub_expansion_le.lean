import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic
import P2M.Util
import P2M.Sol.S_RegularSingular_hasDerivAt_coeff_inv_smul_fold_of_system_of_norm_sub_expansion_le

set_option autoImplicit false

theorem RegularSingular.hasDerivAt_coeff_inv_smul_fold_of_system_of_norm_sub_expansion_le
    {n J R d d₂ : ℕ} (e : Fin n → ℂ) (he : Function.Injective e) (ρ δ : ℝ) (hδ : 0 < δ)
    (hre : ∀ i, (e i).re ≤ ρ)
    (hcl : ∀ (i : Fin n) (m : ℕ), (e i + m).re ≤ ρ → ∃ i', e i' = e i + m)
    (hgap : ∀ (i : Fin n) (m : ℕ), ρ < (e i + m).re → ρ + 2 * δ ≤ (e i + m).re)
    (Mc : Fin (d₂ + 1) → Matrix (Fin R) (Fin R) ℂ)
    (A : Fin d → Fin (d₂ + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ)))
    (F Fz : ℝ → ℝ → (Fin R → ℂ))
    (hsys : ∀ y ∈ Set.Ioc (0 : ℝ) 1, ∀ z ∈ Set.Ioc (0 : ℝ) 2, HasDerivAt (fun z => F y z) (Fz y z) z ∧
      (z : ℂ) • Fz y z = (fun a => ∑ b, (∑ a' : Fin (d₂ + 1), (y : ℂ) ^ (a' : ℕ) * Mc a' a b) • F y z b) +
        ∑ k : Fin d, ∑ a' : Fin (d₂ + 1), ((z : ℂ) ^ ((k : ℕ) + 1) * (y : ℂ) ^ (a' : ℕ)) • A k a' (F y z))
    (C : Fin n → Fin J → ℝ → (Fin R → ℂ)) (hC : ∀ i j, ContinuousOn (C i j) (Set.Ioc 0 2))
    (hexp : ∀ z₀ ∈ Set.Ioc (0 : ℝ) 2, ∃ K ε : ℝ, 0 < ε ∧ ∀ z ∈ Set.Ioc (0 : ℝ) 2, |z - z₀| < ε →
      ∀ y ∈ Set.Ioc (0 : ℝ) 1,
        ‖F y z - ∑ i : Fin n, ∑ j : Fin J, ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • C i j z‖ ≤
          K * y ^ (ρ + δ)) :
    ∀ (i : Fin n) (j : Fin J), ∀ z ∈ Set.Ioo (0 : ℝ) 2,
      HasDerivAt (C i j)
        ((z : ℂ)⁻¹ • ∑ a : Fin (d₂ + 1), ∑ i' : Fin n, if e i' + (a : ℕ) = e i then
          Matrix.mulVec (Mc a) (C i' j z) + ∑ k : Fin d, ((z : ℂ) ^ ((k : ℕ) + 1)) • A k a (C i' j z)
        else 0) z := by p2m_exact_reverting @_root_.P2MW.S_RegularSingular_hasDerivAt_coeff_inv_smul_fold_of_system_of_norm_sub_expansion_le.solution
