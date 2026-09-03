import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.FieldTheory.Finite.Basic
import P2M.Util
import P2M.Sol.S_CohCarrier_isUnit_index_of_forall_mem_iff_castHom_eq_one

set_option autoImplicit false

open IsLocalRing

theorem CohCarrier.isUnit_index_of_forall_mem_iff_castHom_eq_one
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (N r : ℕ) [NeZero N] (hr : r.Prime) (hr1 : ¬ p ∣ r - 1) [NeZero (N * r)]
    (H₀ : Subgroup (ZMod (N * r))ˣ)
    (hH₀ : ∀ v : (ZMod (N * r))ˣ, v ∈ H₀ ↔ ZMod.castHom (dvd_mul_left r N) (ZMod r) (v : ZMod (N * r)) = 1) :
    IsUnit ((H₀.index : ℕ) : 𝒪) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_isUnit_index_of_forall_mem_iff_castHom_eq_one.solution
