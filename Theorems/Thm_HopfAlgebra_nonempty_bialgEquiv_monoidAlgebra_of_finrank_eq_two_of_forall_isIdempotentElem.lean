import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_finrank_eq_two_of_forall_isIdempotentElem

universe u v
theorem HopfAlgebra.nonempty_bialgEquiv_monoidAlgebra_of_finrank_eq_two_of_forall_isIdempotentElem
    {R : Type u} [CommRing R] (h2 : Irreducible (2 : R))
    (H : Type v) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H]
    (hrank : Module.finrank R H = 2) (hconn : ∀ e : H, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Nonempty (H ≃ₐc[R] MonoidAlgebra R (Multiplicative (ZMod 2))) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_finrank_eq_two_of_forall_isIdempotentElem.solution
