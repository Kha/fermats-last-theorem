import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_exists_sq_ne_one_and_forall_charpoly_torus_mul_eq_prod_of_forall_character_eq

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.exists_sq_ne_one_and_forall_charpoly_torus_mul_eq_prod_of_forall_character_eq
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    (ρ : Representation K (GL2 q) V)
    (hcent : ∀ c : (ZMod q)ˣ, ρ (scalarElem q c) = LinearMap.id)
    (hK1 : Module.finrank K V = q - 1)
    (hK2 : ∀ (c : (ZMod q)ˣ) (g : GL2 q), ρ.character (scalarElem q c * g) = ρ.character g)
    (hK3 : ∀ t : ZMod q, t ≠ 0 → ρ.character (unipotent q t) = -1)
    (hK4 : ∀ (a : (ZMod q)ˣ) (s : ZMod q), a ≠ 1 → ρ.character (unipotent q s * diagElem q a) = 0)
    (hK5 : ∑ g : GL2 q, ρ.character g = 0)
    (hK6 : ∑ g : GL2 q, ρ.character g * ρ.character g⁻¹ = Nat.card (GL2 q))
    (S₀ : Finset ((GaloisField q 2)ˣ →* Kˣ)) (hS₀ : ∀ μ : (GaloisField q 2)ˣ →* Kˣ,
      μ ∈ S₀ ↔ ∀ c : (ZMod q)ˣ, μ (Units.map (algebraMap (ZMod q) (GaloisField q 2)).toMonoidHom c) = 1) :
    ∃ θ ∈ S₀, θ ^ 2 ≠ 1 ∧ ∀ α : (GaloisField q 2)ˣ,
      (ρ (torus q α)).charpoly * ((X - C ((θ α : Kˣ) : K)) * (X - C (((θ α)⁻¹ : Kˣ) : K))) =
        ∏ μ ∈ S₀, (X - C ((μ α : Kˣ) : K)) := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_exists_sq_ne_one_and_forall_charpoly_torus_mul_eq_prod_of_forall_character_eq.solution
