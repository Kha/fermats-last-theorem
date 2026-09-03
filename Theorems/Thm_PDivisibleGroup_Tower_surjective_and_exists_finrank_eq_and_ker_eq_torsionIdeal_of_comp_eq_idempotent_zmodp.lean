import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_Tower_surjective_and_exists_finrank_eq_and_ker_eq_torsionIdeal_of_comp_eq_idempotent_zmodp
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient
attribute [-simp] PDivisibleGroup.Tower.levelCast_rfl PDivisibleGroup.Tower.transitionLE_one PDivisibleGroup.Tower.transitionLE_zero PDivisibleGroup.Hopf.nsmulBialgHom_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.Tower.surjective_and_exists_finrank_eq_and_ker_eq_torsionIdeal_of_comp_eq_idempotent_zmodp
    (p : ℕ) [Fact p.Prime] (h : ℕ)
    (B : ℕ → Type) [∀ n, CommRing (B n)] [∀ n, HopfAlgebra (ZMod p) (B n)]
    [∀ n, Coalgebra.IsCocomm (ZMod p) (B n)] [∀ n, Module.Finite (ZMod p) (B n)]
    (s : ∀ n, B (n + 1) →ₐc[ZMod p] B n) (hs : ∀ n, Function.Surjective (s n))
    (hrankB : ∀ n, Module.finrank (ZMod p) (B n) = p ^ (n * h))
    (hkerB : ∀ n, RingHom.ker (s n) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (B (n + 1)) (p ^ n))

    (e : ∀ n, B n →ₐc[ZMod p] B n) (he : ∀ n, (e n).comp (e n) = e n)
    (het : ∀ n, (s n).comp (e (n + 1)) = (e n).comp (s n))
    (C : ℕ → Type) [∀ n, CommRing (C n)] [∀ n, HopfAlgebra (ZMod p) (C n)]
    [∀ n, Coalgebra.IsCocomm (ZMod p) (C n)] [∀ n, Module.Finite (ZMod p) (C n)]
    (q : ∀ n, B n →ₐc[ZMod p] C n) (i : ∀ n, C n →ₐc[ZMod p] B n)
    (hq : ∀ n, Function.Surjective (q n))
    (hqi : ∀ n, (q n).comp (i n) = BialgHom.id (ZMod p) (C n))
    (hiq : ∀ n, (i n).comp (q n) = e n) :
    (∀ n, Function.Surjective ((q n).comp ((s n).comp (i (n + 1))))) ∧
    (∃ h₁ : ℕ, h₁ ≤ h ∧ ∀ n, Module.finrank (ZMod p) (C n) = p ^ (n * h₁)) ∧
    (∀ n, RingHom.ker ((q n).comp ((s n).comp (i (n + 1)))) =
      PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (C (n + 1)) (p ^ n)) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_Tower_surjective_and_exists_finrank_eq_and_ker_eq_torsionIdeal_of_comp_eq_idempotent_zmodp.solution
