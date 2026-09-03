import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_free_quotient_map_ker_counit_of_comp_eq_nsmulAlgHom
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul

universe u v w

theorem PDivisibleGroup.free_quotient_map_ker_counit_of_comp_eq_nsmulAlgHom
    (O : Type u) [CommRing O] [IsDomain O] [IsLocalRing O] (p : ℕ) [Fact p.Prime] (h : ℕ)
    (L : ℕ → Type v) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra O (L v)]
    [∀ v, Coalgebra.IsCocomm O (L v)] [∀ v, Module.Free O (L v)] [∀ v, Module.Finite O (L v)]
    (t : ∀ v, L (v + 1) →ₐc[O] L v) (ht : ∀ v, Function.Surjective (t v))
    (hrankL : ∀ v, Module.finrank O (L v) = p ^ (v * h))
    (hkerL : ∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal O (L (v + 1)) (p ^ v))
    (L' : ℕ → Type w) [∀ v, CommRing (L' v)] [∀ v, HopfAlgebra O (L' v)]
    [∀ v, Coalgebra.IsCocomm O (L' v)] [∀ v, Module.Free O (L' v)] [∀ v, Module.Finite O (L' v)]
    (t' : ∀ v, L' (v + 1) →ₐc[O] L' v) (ht' : ∀ v, Function.Surjective (t' v))
    (hrankL' : ∀ v, Module.finrank O (L' v) = p ^ (v * h))
    (hkerL' : ∀ v, RingHom.ker (t' v) = PDivisibleGroup.Hopf.torsionIdeal O (L' (v + 1)) (p ^ v))
    (f : ∀ v, L' v →ₐc[O] L v) (hf : ∀ u, (f u).comp (t' u) = (t u).comp (f (u + 1)))
    (g : ∀ v, L v →ₐc[O] L' v) (hg : ∀ u, (g u).comp (t u) = (t' u).comp (g (u + 1)))
    (w : ℕ)
    (hgf : ∀ u, (f u : L' u →ₐ[O] L u).comp (g u : L u →ₐ[O] L' u) =
      PDivisibleGroup.Hopf.nsmulAlgHom O (L u) (p ^ w))
    (hfg : ∀ u, (g u : L u →ₐ[O] L' u).comp (f u : L' u →ₐ[O] L u) =
      PDivisibleGroup.Hopf.nsmulAlgHom O (L' u) (p ^ w))
    (v : ℕ) (hv : w ≤ v) :
    Module.Free O (L v ⧸ Ideal.map (f v : L' v →ₐ[O] L v)
        (RingHom.ker (Bialgebra.counitAlgHom O (L' v)))) ∧
    Module.Free O (L' v ⧸ Ideal.map (g v : L v →ₐ[O] L' v)
        (RingHom.ker (Bialgebra.counitAlgHom O (L v)))) ∧
    Module.finrank O (L v ⧸ Ideal.map (f v : L' v →ₐ[O] L v)
        (RingHom.ker (Bialgebra.counitAlgHom O (L' v)))) *
      Module.finrank O (L' v ⧸ Ideal.map (g v : L v →ₐ[O] L' v)
        (RingHom.ker (Bialgebra.counitAlgHom O (L v)))) = p ^ (w * h) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_free_quotient_map_ker_counit_of_comp_eq_nsmulAlgHom.solution
