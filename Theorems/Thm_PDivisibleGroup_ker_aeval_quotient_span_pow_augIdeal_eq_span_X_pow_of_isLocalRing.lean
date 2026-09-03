import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_ker_aeval_quotient_span_pow_augIdeal_eq_span_X_pow_of_isLocalRing
attribute [-instance] MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl
attribute [-simp] CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul

universe v

theorem PDivisibleGroup.ker_aeval_quotient_span_pow_augIdeal_eq_span_X_pow_of_isLocalRing
    (p : ℕ) [Fact p.Prime] (h₀ : ℕ)
    (H : ℕ → Type v) [∀ v, CommRing (H v)] [∀ v, HopfAlgebra (ZMod p) (H v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (H v)] [∀ v, Module.Finite (ZMod p) (H v)]
    (s : ∀ v, H (v + 1) →ₐc[ZMod p] H v) (hs : ∀ v, Function.Surjective (s v))
    (hrankH : ∀ v, Module.finrank (ZMod p) (H v) = p ^ (v * h₀))
    (hkerH : ∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (H (v + 1)) (p ^ v))
    (hlocH : ∀ v, IsLocalRing (H v))
    (n w : ℕ) (hnw : n ≤ w) (d : ℕ)
    (hd : Module.finrank (ZMod p) (PDivisibleGroup.Hopf.augIdeal (ZMod p) (H 1)).Cotangent = d)
    (x : Fin d → H w) (hx : ∀ i, x i ∈ PDivisibleGroup.Hopf.augIdeal (ZMod p) (H w))
    (hspan : Submodule.span (ZMod p) (Set.range fun i =>
      (PDivisibleGroup.Hopf.augIdeal (ZMod p) (H w)).toCotangent ⟨x i, hx i⟩) = ⊤) :
    Function.Surjective ((Ideal.Quotient.mkₐ (ZMod p) (Ideal.span ((fun a : H w => a ^ p ^ n) ''
          (PDivisibleGroup.Hopf.augIdeal (ZMod p) (H w) : Set (H w))))).comp
        (MvPolynomial.aeval x)) ∧
    RingHom.ker ((Ideal.Quotient.mkₐ (ZMod p) (Ideal.span ((fun a : H w => a ^ p ^ n) ''
          (PDivisibleGroup.Hopf.augIdeal (ZMod p) (H w) : Set (H w))))).comp
        (MvPolynomial.aeval x) : MvPolynomial (Fin d) (ZMod p) →ₐ[ZMod p] _) =
      Ideal.span (Set.range fun i : Fin d => (MvPolynomial.X i : MvPolynomial (Fin d) (ZMod p)) ^ p ^ n) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_ker_aeval_quotient_span_pow_augIdeal_eq_span_X_pow_of_isLocalRing.solution
