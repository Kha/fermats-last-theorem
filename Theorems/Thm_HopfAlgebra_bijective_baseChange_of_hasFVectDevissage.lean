import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Definitions.Def_HopfAlgebra_FVectStructure
import Definitions.Def_HopfAlgebra_HasFVectDevissage
import P2M.Util
import P2M.Sol.S_HopfAlgebra_bijective_baseChange_of_hasFVectDevissage
attribute [-instance] MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra
attribute [-simp] HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply

set_option autoImplicit false

universe u v

open scoped TensorProduct

theorem HopfAlgebra.bijective_baseChange_of_hasFVectDevissage
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
    [Coalgebra.IsCocomm R H]
    {H' : Type v} [CommRing H'] [HopfAlgebra R H'] [Module.Finite R H'] [Module.Flat R H']
    [Coalgebra.IsCocomm R H']
    (φ : H →ₐc[R] H') (hφK : Function.Bijective ((φ : H →ₐ[R] H').toLinearMap.baseChange K))
    (R₂ : Type u) [CommRing R₂] [IsDomain R₂] [IsDiscreteValuationRing R₂] [Algebra R R₂]
    [Module.FaithfullyFlat R R₂]
    (K₂ : Type u) [Field K₂] [Algebra R₂ K₂] [IsFractionRing R₂ K₂]
    (hunif₂ : Irreducible (p : R₂))
    (hdev : HopfAlgebra.HasFVectDevissage R₂ K₂ p (K₂ ⊗[R₂] (R₂ ⊗[R] H'))) :
    Function.Bijective ((φ : H →ₐ[R] H').toLinearMap.baseChange R₂) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_bijective_baseChange_of_hasFVectDevissage.solution
