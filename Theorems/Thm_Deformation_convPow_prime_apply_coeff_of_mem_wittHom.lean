import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import P2M.Util
import P2M.Sol.S_Deformation_convPow_prime_apply_coeff_of_mem_wittHom

universe u v w

theorem Deformation.convPow_prime_apply_coeff_of_mem_wittHom
    (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type v) [CommRing A] [Bialgebra k A]
    (T : Type w) [CommRing T] [Algebra k T] (β : WithConv (A →ₗ[k] T))
    {n : ℕ} {x : TruncatedWittVector p n A} (hx : x ∈ Deformation.wittHom k p n A) :
    (∀ h : 0 < n, (β ^ p).ofConv (x.coeff ⟨0, h⟩) = 0) ∧
    ∀ (i : ℕ) (hi : i + 1 < n),
      (β ^ p).ofConv (x.coeff ⟨i + 1, hi⟩) = (β.ofConv (x.coeff ⟨i, Nat.lt_of_succ_lt hi⟩)) ^ p := by p2m_exact_reverting @_root_.P2MW.S_Deformation_convPow_prime_apply_coeff_of_mem_wittHom.solution
