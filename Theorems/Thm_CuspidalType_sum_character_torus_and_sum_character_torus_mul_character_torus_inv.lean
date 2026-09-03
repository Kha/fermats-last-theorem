import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_sum_character_torus_and_sum_character_torus_mul_character_torus_inv

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.sum_character_torus_and_sum_character_torus_mul_character_torus_inv
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    [Fintype (GaloisField q 2)ˣ] (ρ : Representation K (GL2 q) V)
    (hK1 : Module.finrank K V = q - 1)
    (hK2 : ∀ (c : (ZMod q)ˣ) (g : GL2 q), ρ.character (scalarElem q c * g) = ρ.character g)
    (hK3 : ∀ t : ZMod q, t ≠ 0 → ρ.character (unipotent q t) = -1)
    (hK4 : ∀ (a : (ZMod q)ˣ) (s : ZMod q), a ≠ 1 → ρ.character (unipotent q s * diagElem q a) = 0)
    (hK5 : ∑ g : GL2 q, ρ.character g = 0)
    (hK6 : ∑ g : GL2 q, ρ.character g * ρ.character g⁻¹ = Nat.card (GL2 q)) :
    ∑ α : (GaloisField q 2)ˣ, ρ.character (torus q α) = ((q ^ 2 - 1 : ℕ) : K) ∧
    ∑ α : (GaloisField q 2)ˣ, ρ.character (torus q α) * ρ.character (torus q α)⁻¹ =
      (((q - 1) * (q ^ 2 - 1) : ℕ) : K) := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_sum_character_torus_and_sum_character_torus_mul_character_torus_inv.solution
