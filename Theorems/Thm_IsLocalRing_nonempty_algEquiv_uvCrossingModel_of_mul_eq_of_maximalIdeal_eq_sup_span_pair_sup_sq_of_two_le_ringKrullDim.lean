import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_IsLocalRing_nonempty_algEquiv_uvCrossingModel_of_mul_eq_of_maximalIdeal_eq_sup_span_pair_sup_sq_of_two_le_ringKrullDim
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

theorem IsLocalRing.nonempty_algEquiv_uvCrossingModel_of_mul_eq_of_maximalIdeal_eq_sup_span_pair_sup_sq_of_two_le_ringKrullDim
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (ϖ : O) (hϖ : Irreducible ϖ)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra O R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (hres : Function.Surjective ((IsLocalRing.residue R).comp (algebraMap O R)))
    (u v : R) (huv : u * v = algebraMap O R ϖ)
    (huv' : IsLocalRing.maximalIdeal R =
      (IsLocalRing.maximalIdeal O).map (algebraMap O R) ⊔ Ideal.span {u, v} ⊔ (IsLocalRing.maximalIdeal R) ^ 2)
    (hdim : 2 ≤ ringKrullDim R) :
    Nonempty (R ≃ₐ[O] ModularCurve.UVCrossingModel O ϖ) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_nonempty_algEquiv_uvCrossingModel_of_mul_eq_of_maximalIdeal_eq_sup_span_pair_sup_sq_of_two_le_ringKrullDim.solution
