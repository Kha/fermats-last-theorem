import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_exists_multiplicity_of_isCyclic

set_option autoImplicit false

open Polynomial

theorem Representation.exists_multiplicity_of_isCyclic {C K V : Type*} [CommGroup C] [Fintype C] [IsCyclic C]
    [Field K] [IsAlgClosed K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (τ : Representation K C V) :
    ∃ m : (C →* Kˣ) →₀ ℕ,
      (∀ c, LinearMap.trace K V (τ c) = m.sum fun μ n => (n : K) * ((μ c : Kˣ) : K)) ∧
      (∀ c, (τ c).charpoly = m.prod fun μ n => (X - Polynomial.C ((μ c : Kˣ) : K)) ^ n) ∧
      (m.sum fun _ n => n) = Module.finrank K V ∧
      (∀ μ ∈ m.support, ∀ c, τ c = LinearMap.id → μ c = 1) := by p2m_exact_reverting @_root_.P2MW.S_Representation_exists_multiplicity_of_isCyclic.solution
