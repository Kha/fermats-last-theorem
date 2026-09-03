import Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Finite
import P2M.Util
import P2M.Sol.S_CuspidalType_IsCuspidalOfType_baseChange

set_option autoImplicit false

open scoped TensorProduct

namespace CuspidalType

theorem IsCuspidalOfType.baseChange
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {θ : (GaloisField q 2)ˣ →* Kˣ} {σ : Representation K (GL2 q) V} (h : IsCuspidalOfType θ σ)
    (K' : Type*) [Field K'] [Algebra K K'] :
    IsCuspidalOfType ((Units.map (algebraMap K K').toMonoidHom).comp θ)
      ((Module.End.baseChangeHom K K' V : Module.End K V →* Module.End K' (K' ⊗[K] V)).comp σ) := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_IsCuspidalOfType_baseChange.solution
