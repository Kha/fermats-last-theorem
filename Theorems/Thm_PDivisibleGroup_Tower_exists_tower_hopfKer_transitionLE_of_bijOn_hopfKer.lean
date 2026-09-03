import Mathlib
import Definitions.Def_PDivisibleGroup_Tower
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_Tower_exists_tower_hopfKer_transitionLE_of_bijOn_hopfKer
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl
attribute [-simp] HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul

set_option autoImplicit false

theorem PDivisibleGroup.Tower.exists_tower_hopfKer_transitionLE_of_bijOn_hopfKer
    {R : Type} [CommRing R] [IsLocalRing R] [IsDomain R] [IsPrincipalIdealRing R] (p h' i₀ : ℕ)
    (B : ℕ → Type) [∀ w, CommRing (B w)] [∀ w, HopfAlgebra R (B w)]
    [∀ w, Coalgebra.IsCocomm R (B w)] [∀ w, Module.Finite R (B w)] [∀ w, Module.Free R (B w)]
    (t : ∀ w, B (w + 1) →ₐc[R] B w) (ht : ∀ w, Function.Surjective (t w))
    (m : ∀ w, B w →ₐc[R] B (w + 1))
    (hmt : ∀ w, (m w).comp (t w) = PDivisibleGroup.Hopf.nsmulBialgHom R (B (w + 1)) p)
    (htm : ∀ w, (t w).comp (m w) = PDivisibleGroup.Hopf.nsmulBialgHom R (B w) p)
    (hkill : ∀ w, ∀ d ∈ HopfAlgebra.hopfKer (t w),
      PDivisibleGroup.Hopf.nsmulAlgHom R (B (w + 1)) p d = algebraMap R (B (w + 1)) (Coalgebra.counit d))
    (hmaps : ∀ w, Set.MapsTo (m (w + 1)) (HopfAlgebra.hopfKer (t w) : Set (B (w + 1)))
      (HopfAlgebra.hopfKer (t (w + 1)) : Set (B (w + 2))))
    (hbij : ∀ w, i₀ ≤ w → Set.BijOn (m (w + 1)) (HopfAlgebra.hopfKer (t w) : Set (B (w + 1)))
      (HopfAlgebra.hopfKer (t (w + 1)) : Set (B (w + 2))))
    (hrank : Module.finrank R ↥(HopfAlgebra.hopfKer (t i₀)) = p ^ h') :
    ∃ (L : ℕ → Type) (_ : ∀ v, CommRing (L v)) (_ : ∀ v, HopfAlgebra R (L v))
      (_ : ∀ v, Coalgebra.IsCocomm R (L v)) (_ : ∀ v, Module.Free R (L v)) (_ : ∀ v, Module.Finite R (L v))
      (t' : ∀ v, L (v + 1) →ₐc[R] L v) (ι : ∀ v, L v →ₐc[R] B (i₀ + v)),
      (∀ v, Function.Surjective (t' v)) ∧ (∀ v, Module.finrank R (L v) = p ^ (v * h')) ∧
      (∀ v, RingHom.ker (t' v) = PDivisibleGroup.Hopf.torsionIdeal R (L (v + 1)) (p ^ v)) ∧
      (∀ v, Function.Injective (ι v)) ∧
      (∀ v, (ι v : L v →ₐ[R] B (i₀ + v)).range =
        HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ v)) ∧
      (∀ v, (ι v).comp (t' v) = (t (i₀ + v)).comp (ι (v + 1))) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_Tower_exists_tower_hopfKer_transitionLE_of_bijOn_hopfKer.solution
