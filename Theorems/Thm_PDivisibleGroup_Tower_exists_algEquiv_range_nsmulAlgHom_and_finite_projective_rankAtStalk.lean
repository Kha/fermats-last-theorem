import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Tower
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_Tower_exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk
attribute [-instance] HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient
attribute [-simp] HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk

universe u v

theorem PDivisibleGroup.Tower.exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk
    {R : Type u} [CommRing R] (p h : ℕ)
    (L : ℕ → Type v) [∀ w, CommRing (L w)] [∀ w, HopfAlgebra R (L w)]
    [∀ w, Coalgebra.IsCocomm R (L w)] [∀ w, Module.Free R (L w)] [∀ w, Module.Finite R (L w)]
    (t : ∀ w, L (w + 1) →ₐc[R] L w) (ht : ∀ w, Function.Surjective (t w))
    (hrankL : ∀ w, Module.finrank R (L w) = p ^ (w * h))
    (hkerL : ∀ w, RingHom.ker (t w) = PDivisibleGroup.Hopf.torsionIdeal R (L (w + 1)) (p ^ w))
    (v u : ℕ) :
    (∃ e : L v ≃ₐ[R] ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).range,
        ∀ a : L (v + u),
          ((e (PDivisibleGroup.Tower.transitionLE t v u a) :
              ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).range) : L (v + u)) =
            PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u) a) ∧
      Module.Finite ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).range (L (v + u)) ∧
      Module.Projective ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).range (L (v + u)) ∧
      (∃ r : L (v + u) →ₗ[↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).range]
          ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).range,
        ∀ c : ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).range,
          r (c : L (v + u)) = c) ∧
      ∀ 𝔮 : PrimeSpectrum ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).range,
        Module.rankAtStalk (R := ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).range)
          (L (v + u)) 𝔮 = p ^ (u * h) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_Tower_exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk.solution
