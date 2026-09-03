import Mathlib
import Definitions.Def_ModularCurve_SL2Elementary
import P2M.Util
import P2M.Sol.S_Matrix_SpecialLinearGroup_borel_orbit_structure_of_sylow_eq_upper

set_option autoImplicit false

open Matrix MatrixGroups

theorem Matrix.SpecialLinearGroup.borel_orbit_structure_of_sylow_eq_upper
    {K : Type} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    {H : Type} [Group H] [Finite H] (ρ : H →* SL(2, K)) (hρ : Function.Injective ρ)
    (P : Sylow p H) (hP : ∀ x : H, x ∈ P ↔ ∃ t : K, ρ x = ModularCurve.upperElem t)
    (hne : ∃ a : K, a ≠ 0 ∧ ∃ u : H,
      ((ρ u : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, a; 0, 1]) :
    Nat.card (Subgroup.normalizer (P : Set H)) =
      Nat.card P * Nat.card (Set.range fun x : Subgroup.normalizer (P : Set H) =>
        ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0) ∧
    Nat.card (Set.range fun x : Subgroup.normalizer (P : Set H) =>
        ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0) =
      Nat.card {x : H // ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 ∨
          ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1} *
        Nat.card (Set.range fun x : Subgroup.normalizer (P : Set H) =>
          (((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0) ^ 2) ∧
    (Nat.card (Set.range fun x : Subgroup.normalizer (P : Set H) =>
        (((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0) ^ 2) ≠ 1 →
      ∃ b : H, b ∈ Subgroup.normalizer (P : Set H) ∧
        (((ρ b : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 +
          ((ρ b : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 1) ^ 2 ≠ 4 ∧
        Nat.card (Subgroup.centralizer ({b} : Set H)) =
          Nat.card (Set.range fun x : Subgroup.normalizer (P : Set H) =>
            ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0) ∧
        ((∃ n₀ : H, n₀ ∈ Subgroup.normalizer (Subgroup.centralizer ({b} : Set H) : Set H) ∧
            n₀ ∉ Subgroup.centralizer ({b} : Set H)) →
          ∃ k : ℕ, Nat.card (Sylow p H) = 1 + Nat.card P + k * (Nat.card P *
            Nat.card (Set.range fun x : Subgroup.normalizer (P : Set H) =>
              (((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0) ^ 2))) ∧
        (∀ h : H, (((ρ h : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 +
            ((ρ h : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 1) ^ 2 ≠ 4 →
          (¬ ∃ s : H, ∀ g : H, g ∈ Subgroup.centralizer ({h} : Set H) ↔
              s⁻¹ * g * s ∈ Subgroup.centralizer ({b} : Set H)) →
          Nat.card (Subgroup.centralizer ({h} : Set H)) ∣
            Nat.card {x : H // ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 ∨
              ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1} * Nat.card (Sylow p H))) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_SpecialLinearGroup_borel_orbit_structure_of_sylow_eq_upper.solution
