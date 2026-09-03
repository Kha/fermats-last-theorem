import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_PDivisibleGroup_Basic
import P2M.Util
import P2M.Sol.S_HopfAlgebra_le_finrank_primitives_of_finrank_eq_pow_of_nsmulAlgHom_eq

set_option autoImplicit false

universe u v

theorem HopfAlgebra.le_finrank_primitives_of_finrank_eq_pow_of_nsmulAlgHom_eq
    (K : Type u) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (H : Type v) [CommRing H] [HopfAlgebra K H] [Coalgebra.IsCocomm K H] [Module.Finite K H]
    (g : ℕ) (hH : Module.finrank K H = p ^ (2 * g))
    (hp : PDivisibleGroup.Hopf.nsmulAlgHom K H p = (Algebra.ofId K H).comp (Bialgebra.counitAlgHom K H))
    (hcot : Module.finrank K (RingHom.ker (Bialgebra.counitAlgHom K H)).Cotangent = g) :
    g ≤ Module.finrank K ↥(primitives K H) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_le_finrank_primitives_of_finrank_eq_pow_of_nsmulAlgHom_eq.solution
