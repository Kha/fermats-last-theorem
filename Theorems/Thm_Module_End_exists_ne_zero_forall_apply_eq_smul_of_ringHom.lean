import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.Module.LinearMap.End
import P2M.Util
import P2M.Sol.S_Module_End_exists_ne_zero_forall_apply_eq_smul_of_ringHom

theorem Module.End.exists_ne_zero_forall_apply_eq_smul_of_ringHom {K V T : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] [CommRing T] (ρ : T →+* Module.End K V) (L : Submodule ℤ V) (hL : L.FG) (hstab : ∀ (t : T), ∀ x ∈ L, ρ t x ∈ L) (hfaith : ∀ t : T, (∀ x ∈ L, ρ t x = 0) → t = 0) (hfree : ∀ (n : ℕ) (y : Fin n → V), (∀ i, y i ∈ L) → LinearIndependent ℤ y → LinearIndependent K y) (χ : T →+* K) : ∃ v : V, v ≠ 0 ∧ ∀ t : T, ρ t v = χ t • v := by p2m_exact_reverting @_root_.P2MW.S_Module_End_exists_ne_zero_forall_apply_eq_smul_of_ringHom.solution
