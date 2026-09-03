import Mathlib
import P2M.Util
import P2M.Sol.S_Module_nonempty_dual_quotient_range_dualMap_linearEquiv_quotient_of_forall_surjective_iff

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.nonempty_dual_quotient_range_dualMap_linearEquiv_quotient_of_forall_surjective_iff
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (K₀ K₁ : Type u) [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Free R K₀]
    [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Free R K₁]
    (d : K₀ →ₗ[R] K₁)
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) (hIN : ∃ N : ℕ, IsLocalRing.maximalIdeal R ^ N ≤ I)
    (hU : Module.finrank (R ⧸ IsLocalRing.maximalIdeal R)
      (LinearMap.ker (d.baseChange (R ⧸ IsLocalRing.maximalIdeal R))) = 1)
    (hW : ∀ (J' : Ideal R) (hJ' : J' ≤ IsLocalRing.maximalIdeal R), (∃ N : ℕ, IsLocalRing.maximalIdeal R ^ N ≤ J') →
      ((∀ z : (R ⧸ IsLocalRing.maximalIdeal R) ⊗[R] K₀, d.baseChange (R ⧸ IsLocalRing.maximalIdeal R) z = 0 →
          ∃ w : (R ⧸ J') ⊗[R] K₀, d.baseChange (R ⧸ J') w = 0 ∧
            LinearMap.rTensor K₀ (Submodule.factor hJ') w = z) ↔ I ≤ J')) :
    Nonempty ((Module.Dual R K₀ ⧸ LinearMap.range d.dualMap) ≃ₗ[R] (R ⧸ I)) := by p2m_exact_reverting @_root_.P2MW.S_Module_nonempty_dual_quotient_range_dualMap_linearEquiv_quotient_of_forall_surjective_iff.solution
