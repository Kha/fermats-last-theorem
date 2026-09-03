import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_Dieudonne_ModpRealization
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_primitives_linearEquiv_dual_cotangent_cartierDual

set_option autoImplicit false

universe u v

theorem HopfAlgebra.exists_primitives_linearEquiv_dual_cotangent_cartierDual
    (k : Type u) [Field k] (H : Type v) [CommRing H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H]
    [Module.Finite k H] :
    ∃ e : ↥(primitives k H) ≃ₗ[k]
        Module.Dual k (RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k H))).Cotangent,
      ∀ (x : ↥(primitives k H)) (φ : CartierDual k H)
        (hφ : φ ∈ RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k H))),
        e x ((RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k H))).toCotangent ⟨φ, hφ⟩) = φ (x : H) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_primitives_linearEquiv_dual_cotangent_cartierDual.solution
