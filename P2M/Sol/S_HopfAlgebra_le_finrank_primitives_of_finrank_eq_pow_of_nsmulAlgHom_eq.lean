import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_PDivisibleGroup_Basic
import Theorems.Thm_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent
import Theorems.Thm_HopfAlgebra_exists_primitives_linearEquiv_dual_cotangent_cartierDual
import Theorems.Thm_HopfAlgebra_finrank_span_pow_prime_le_finrank_cartierDual_quotient_of_nsmulAlgHom_eq
import Theorems.Thm_HopfAlgebra_finrank_le_finrank_span_pow_prime_mul_pow_finrank_cotangent
import P2M.Util
namespace P2MW.S_HopfAlgebra_le_finrank_primitives_of_finrank_eq_pow_of_nsmulAlgHom_eq

set_option autoImplicit false

universe u v

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (H : Type v) [CommRing H] [HopfAlgebra K H] [Coalgebra.IsCocomm K H] [Module.Finite K H]
    (g : ℕ) (hH : Module.finrank K H = p ^ (2 * g))
    (hp : PDivisibleGroup.Hopf.nsmulAlgHom K H p = (Algebra.ofId K H).comp (Bialgebra.counitAlgHom K H))
    (hcot : Module.finrank K (RingHom.ker (Bialgebra.counitAlgHom K H)).Cotangent = g) :
    g ≤ Module.finrank K ↥(primitives K H) := by

  have h905 := HopfAlgebra.finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent K p (CartierDual K H)

  obtain ⟨eqv, -⟩ := HopfAlgebra.exists_primitives_linearEquiv_dual_cotangent_cartierDual K H
  have h4 : Module.finrank K ↥(primitives K H) =
      Module.finrank K (RingHom.ker (Bialgebra.counitAlgHom K (CartierDual K H))).Cotangent :=
    eqv.finrank_eq.trans Subspace.dual_finrank_eq

  have h5 := HopfAlgebra.finrank_span_pow_prime_le_finrank_cartierDual_quotient_of_nsmulAlgHom_eq K p H hp

  have h6 := HopfAlgebra.finrank_le_finrank_span_pow_prime_mul_pow_finrank_cotangent K p H
  rw [hH, hcot] at h6
  rw [h905, ← h4] at h5
  have hchain : p ^ (2 * g) ≤ p ^ (Module.finrank K ↥(primitives K H) + g) := by
    calc p ^ (2 * g) ≤ Module.finrank K ↥(Submodule.span K (Set.range fun a : H => a ^ p)) * p ^ g := h6
      _ ≤ p ^ Module.finrank K ↥(primitives K H) * p ^ g := Nat.mul_le_mul_right _ h5
      _ = p ^ (Module.finrank K ↥(primitives K H) + g) := (pow_add p _ _).symm
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have := (Nat.pow_le_pow_iff_right hp1).mp hchain
  omega
