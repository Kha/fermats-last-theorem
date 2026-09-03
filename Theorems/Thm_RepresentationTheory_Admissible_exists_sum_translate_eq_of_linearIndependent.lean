import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import P2M.Util
import P2M.Sol.S_RepresentationTheory_Admissible_exists_sum_translate_eq_of_linearIndependent
attribute [-simp] FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors

theorem RepresentationTheory.Admissible.exists_sum_translate_eq_of_linearIndependent
    (G : Type) [Group G] [TopologicalSpace G]
    (V : Submodule ℂ (G → ℂ))
    (hstab : ∀ W ∈ V, ∀ h : G, (fun g => W (g * h)) ∈ V)
    (hirr : ∀ W₀ ∈ V, W₀ ≠ 0 → ∀ W ∈ V,
      W ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => W₀ (g * h)))
    (hadm : ∀ U : Subgroup G, IsOpen (U : Set G) →
      ∃ B : Finset (G → ℂ), ∀ W ∈ V, (∀ k ∈ U, ∀ g : G, W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (G → ℂ)))
    (hsm : ∀ W ∈ V, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, W (g * k) = W g)
    (n : ℕ) (u : Fin n → G → ℂ) (hu : ∀ i, u i ∈ V) (hind : LinearIndependent ℂ u)
    (v : Fin n → G → ℂ) (hv : ∀ i, v i ∈ V) :
    ∃ (m : ℕ) (c : Fin m → ℂ) (x : Fin m → G),
      ∀ i : Fin n, (fun g : G => ∑ j, c j * u i (g * x j)) = v i := by p2m_exact_reverting @_root_.P2MW.S_RepresentationTheory_Admissible_exists_sum_translate_eq_of_linearIndependent.solution
