import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_ringEquiv_adicCompletion_uvCrossingModel_of_mul_eq_of_span_pair
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

theorem IsLocalRing.exists_ringEquiv_adicCompletion_uvCrossingModel_of_mul_eq_of_span_pair
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    (ϖ : O) (hϖ : Irreducible ϖ)
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra O R]
    (x y : R) (hxy : x * y = algebraMap O R ϖ)
    (hm : maximalIdeal R = Ideal.span {x, y})
    (hres : Function.Surjective ((IsLocalRing.residue R).comp (algebraMap O R)))
    (hdim : 2 ≤ ringKrullDim R) :
    ∃ ι : AdicCompletion (maximalIdeal R) R ≃+* UVCrossingModel O ϖ,
      (∀ o : O, ι (algebraMap R _ (algebraMap O R o)) = const ϖ o) ∧
      ι (algebraMap R _ x) = U ϖ ∧
      ι (algebraMap R _ y) = V ϖ := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_ringEquiv_adicCompletion_uvCrossingModel_of_mul_eq_of_span_pair.solution
