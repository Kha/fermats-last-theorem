import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_SpecialLinearGroup_centralizer_semisimple_structure_of_finite

set_option autoImplicit false

open Matrix MatrixGroups

theorem Matrix.SpecialLinearGroup.centralizer_semisimple_structure_of_finite
    {K : Type} [Field K] (h2 : (2 : K) ≠ 0)
    {H : Type} [Group H] [Finite H] (ρ : H →* SL(2, K)) (hρ : Function.Injective ρ)
    (h : H) (hh : (((ρ h : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 +
      ((ρ h : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 1) ^ 2 ≠ 4) :
    (∀ g : H, g ∈ Subgroup.centralizer ({h} : Set H) ↔
      ∃ x y : K, ((ρ g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
        x • (1 : Matrix (Fin 2) (Fin 2) K) + y • ((ρ h : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) ∧
    (∀ g ∈ Subgroup.centralizer ({h} : Set H),
      ¬ (((ρ g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 ∨
         ((ρ g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1) →
      Subgroup.centralizer ({g} : Set H) = Subgroup.centralizer ({h} : Set H) ∧
      ((((ρ g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 +
        ((ρ g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 1) ^ 2 ≠ 4)) ∧
    Nat.card (Subgroup.normalizer (Subgroup.centralizer ({h} : Set H) : Set H)) ≤
      2 * Nat.card (Subgroup.centralizer ({h} : Set H)) ∧
    Nat.card {x : H // ¬ (((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 ∨
        ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1) ∧
      ∃ s : H, ∀ g : H, g ∈ Subgroup.centralizer ({x} : Set H) ↔
        s⁻¹ * g * s ∈ Subgroup.centralizer ({h} : Set H)} *
      Nat.card (Subgroup.normalizer (Subgroup.centralizer ({h} : Set H) : Set H)) =
    Nat.card H * (Nat.card (Subgroup.centralizer ({h} : Set H)) -
      Nat.card {x : H // ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 ∨
        ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1}) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_SpecialLinearGroup_centralizer_semisimple_structure_of_finite.solution
