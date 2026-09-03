import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_LocalNewvector_ConductorDatum
import Definitions.Def_LocalNewvector_ReductionFunctor
import P2M.Util
import P2M.Sol.S_LocalNewvector_isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType

set_option autoImplicit false

theorem LocalNewvector.isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType
    (q : ℕ) [Fact q.Prime]
    (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
    [FiniteDimensional ℂ ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)]
    (hV : LocalNewvector.IsIrreducibleGLRep q V) (θ : (GaloisField q 2)ˣ →* ℂˣ)
    {X : Type*} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] {ρ : Representation ℂ (CuspidalType.GL2 q) X}
    (hρ : CuspidalType.IsCuspidalOfType θ ρ)
    (φ : X →ₗ[ℂ] ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V))
    (hφ : ∀ g x, φ (ρ g x) = LocalNewvector.gl2ReductionRep q V g (φ x)) (hφinj : Function.Injective φ) :
    CuspidalType.IsCuspidalOfType θ (LocalNewvector.gl2ReductionRep q V) := by p2m_exact_reverting @_root_.P2MW.S_LocalNewvector_isCuspidalOfType_gl2ReductionRep_of_isIrreducibleGLRep_of_injective_of_isCuspidalOfType.solution
