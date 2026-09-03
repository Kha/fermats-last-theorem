import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_finrank_quotient_map_ker_counit_mul_eq_pow_of_comp_eq_nsmulAlgHom
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul

universe u v w

theorem PDivisibleGroup.finrank_quotient_map_ker_counit_mul_eq_pow_of_comp_eq_nsmulAlgHom
    (κ : Type u) [Field κ] (p : ℕ) [Fact p.Prime] (h : ℕ)
    (L : ℕ → Type v) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra κ (L v)]
    [∀ v, Coalgebra.IsCocomm κ (L v)] [∀ v, Module.Free κ (L v)] [∀ v, Module.Finite κ (L v)]
    (t : ∀ v, L (v + 1) →ₐc[κ] L v) (ht : ∀ v, Function.Surjective (t v))
    (hrankL : ∀ v, Module.finrank κ (L v) = p ^ (v * h))
    (hkerL : ∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal κ (L (v + 1)) (p ^ v))
    (L' : ℕ → Type w) [∀ v, CommRing (L' v)] [∀ v, HopfAlgebra κ (L' v)]
    [∀ v, Coalgebra.IsCocomm κ (L' v)] [∀ v, Module.Free κ (L' v)] [∀ v, Module.Finite κ (L' v)]
    (t' : ∀ v, L' (v + 1) →ₐc[κ] L' v) (ht' : ∀ v, Function.Surjective (t' v))
    (hrankL' : ∀ v, Module.finrank κ (L' v) = p ^ (v * h))
    (hkerL' : ∀ v, RingHom.ker (t' v) = PDivisibleGroup.Hopf.torsionIdeal κ (L' (v + 1)) (p ^ v))
    (f : ∀ v, L' v →ₐc[κ] L v) (hf : ∀ u, (f u).comp (t' u) = (t u).comp (f (u + 1)))
    (g : ∀ v, L v →ₐc[κ] L' v) (hg : ∀ u, (g u).comp (t u) = (t' u).comp (g (u + 1)))
    (w : ℕ)
    (hgf : ∀ u, (f u : L' u →ₐ[κ] L u).comp (g u : L u →ₐ[κ] L' u) =
      PDivisibleGroup.Hopf.nsmulAlgHom κ (L u) (p ^ w))
    (hfg : ∀ u, (g u : L u →ₐ[κ] L' u).comp (f u : L' u →ₐ[κ] L u) =
      PDivisibleGroup.Hopf.nsmulAlgHom κ (L' u) (p ^ w))
    (v : ℕ) (hv : w ≤ v) :
    Module.finrank κ (L v ⧸ Ideal.map (f v : L' v →ₐ[κ] L v)
        (RingHom.ker (Bialgebra.counitAlgHom κ (L' v)))) *
      Module.finrank κ (L' v ⧸ Ideal.map (g v : L v →ₐ[κ] L' v)
        (RingHom.ker (Bialgebra.counitAlgHom κ (L v)))) = p ^ (w * h) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_finrank_quotient_map_ker_counit_mul_eq_pow_of_comp_eq_nsmulAlgHom.solution
