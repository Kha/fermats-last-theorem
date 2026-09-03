import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_exists_tower_isLocalRing_isReduced_bijective_tensorProduct_comul_zmodp
attribute [-instance] HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul

open scoped TensorProduct

universe v

theorem PDivisibleGroup.exists_tower_isLocalRing_isReduced_bijective_tensorProduct_comul_zmodp
    (p : ℕ) [Fact p.Prime] (h : ℕ)
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v) (hs : ∀ v, Function.Surjective (s v))
    (hrankG : ∀ v, Module.finrank (ZMod p) (G v) = p ^ (v * h))
    (hkerG : ∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (G (v + 1)) (p ^ v)) :
    ∃ (hc he : ℕ)
      (Gc : ℕ → Type v) (_ : ∀ v, CommRing (Gc v)) (_ : ∀ v, HopfAlgebra (ZMod p) (Gc v))
      (_ : ∀ v, Coalgebra.IsCocomm (ZMod p) (Gc v)) (_ : ∀ v, Module.Finite (ZMod p) (Gc v))
      (Ge : ℕ → Type v) (_ : ∀ v, CommRing (Ge v)) (_ : ∀ v, HopfAlgebra (ZMod p) (Ge v))
      (_ : ∀ v, Coalgebra.IsCocomm (ZMod p) (Ge v)) (_ : ∀ v, Module.Finite (ZMod p) (Ge v))
      (sc : ∀ v, Gc (v + 1) →ₐc[ZMod p] Gc v) (se : ∀ v, Ge (v + 1) →ₐc[ZMod p] Ge v)
      (qc : ∀ v, G v →ₐc[ZMod p] Gc v) (πe : ∀ v, G v →ₐc[ZMod p] Ge v)
      (σ : ∀ v, Ge v →ₐc[ZMod p] G v)
      (Θ : ∀ v, G v →ₐc[ZMod p] Gc v ⊗[ZMod p] Ge v),
      hc + he = h ∧
      (∀ v, IsLocalRing (Gc v)) ∧ (∀ v, IsReduced (Ge v)) ∧
      (∀ v, Algebra.FormallyUnramified (ZMod p) (Ge v)) ∧
      (∀ v, Function.Surjective (sc v)) ∧
      (∀ v, Module.finrank (ZMod p) (Gc v) = p ^ (v * hc)) ∧
      (∀ v, RingHom.ker (sc v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (Gc (v + 1)) (p ^ v)) ∧
      (∀ v, Function.Surjective (se v)) ∧
      (∀ v, Module.finrank (ZMod p) (Ge v) = p ^ (v * he)) ∧
      (∀ v, RingHom.ker (se v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (Ge (v + 1)) (p ^ v)) ∧
      (∀ v, Function.Surjective (qc v)) ∧ (∀ v, Function.Surjective (πe v)) ∧
      (∀ v, RingHom.ker (πe v : G v →ₐ[ZMod p] Ge v) = nilradical (G v)) ∧
      (∀ v, (πe v).comp (σ v) = BialgHom.id (ZMod p) (Ge v)) ∧
      (∀ v, RingHom.ker (qc v : G v →ₐ[ZMod p] Gc v) =
        Ideal.map (σ v : Ge v →ₐ[ZMod p] G v)
          (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) (Ge v)))) ∧
      (∀ v, Function.Bijective (Θ v)) ∧
      (∀ v b, Θ v b = Algebra.TensorProduct.map (qc v : G v →ₐ[ZMod p] Gc v)
        (πe v : G v →ₐ[ZMod p] Ge v) (Coalgebra.comul (R := ZMod p) b)) ∧
      (∀ v, (qc v).comp (s v) = (sc v).comp (qc (v + 1))) ∧
      (∀ v, (πe v).comp (s v) = (se v).comp (πe (v + 1))) ∧
      (∀ v, (s v).comp (σ (v + 1)) = (σ v).comp (se v)) ∧
      (∀ v, (Θ v).comp (s v) = (Bialgebra.TensorProduct.map (sc v) (se v)).comp (Θ (v + 1))) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_exists_tower_isLocalRing_isReduced_bijective_tensorProduct_comul_zmodp.solution
