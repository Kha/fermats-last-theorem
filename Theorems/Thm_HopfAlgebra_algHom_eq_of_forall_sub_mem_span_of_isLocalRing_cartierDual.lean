import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_HopfAlgebra_algHom_eq_of_forall_sub_mem_span_of_isLocalRing_cartierDual

universe u v w w'

theorem HopfAlgebra.algHom_eq_of_forall_sub_mem_span_of_isLocalRing_cartierDual
    (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (p : ℕ) [Fact p.Prime] (hunif : Irreducible (p : O))
    (k : Type v) [Field k] [Algebra O k] (hk : Function.Surjective (algebraMap O k))
    (hker : RingHom.ker (algebraMap O k) = Ideal.span {(p : O)})
    (H : Type w) [CommRing H] [HopfAlgebra O H] [Coalgebra.IsCocomm O H]
    [Module.Finite O H] [Module.Free O H] (hrank : ∃ a : ℕ, Module.finrank O H = p ^ a)
    (hunip : IsLocalRing (CartierDual k (TensorProduct O k H)))
    (Y : Type w') [CommRing Y] [Algebra O Y] [Module.Finite O Y] [Module.Free O Y]
    (x x' : H →ₐ[O] Y) (hxx' : ∀ h : H, x h - x' h ∈ Ideal.span {(p : Y)}) :
    x = x' := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_algHom_eq_of_forall_sub_mem_span_of_isLocalRing_cartierDual.solution
