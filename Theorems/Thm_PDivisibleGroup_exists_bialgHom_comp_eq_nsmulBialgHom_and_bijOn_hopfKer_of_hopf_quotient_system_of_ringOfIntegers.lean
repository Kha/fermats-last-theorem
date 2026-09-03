import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Tower
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_exists_bialgHom_comp_eq_nsmulBialgHom_and_bijOn_hopfKer_of_hopf_quotient_system_of_ringOfIntegers
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul

set_option autoImplicit false

theorem PDivisibleGroup.exists_bialgHom_comp_eq_nsmulBialgHom_and_bijOn_hopfKer_of_hopf_quotient_system_of_ringOfIntegers
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (M : Submodule ℤ_[p] (TateModule p (G.Points (PadicAlgCl p))))
    (hMstab : ∀ (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p)
        (x : TateModule p (G.Points (PadicAlgCl p))),
      x ∈ M → G.tateModuleRep (PadicAlgCl p) τ x ∈ M)
    (hMsat : ∀ (r : ℤ_[p]) (x : TateModule p (G.Points (PadicAlgCl p))), r ≠ 0 → r • x ∈ M → x ∈ M)
    (B : ℕ → Type) [∀ v, CommRing (B v)] [∀ v, HopfAlgebra (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Coalgebra.IsCocomm (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Module.Finite (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Module.Free (PadicAlgCl.ringOfIntegers p K) (B v)]
    (π : ∀ v, G.level v →ₐc[PadicAlgCl.ringOfIntegers p K] B v)
    (t : ∀ v, B (v + 1) →ₐc[PadicAlgCl.ringOfIntegers p K] B v)
    (hπ : ∀ v, Function.Surjective (π v)) (ht : ∀ v, Function.Surjective (t v))
    (hπt : ∀ v, (π v).comp (G.transition v) = (t v).comp (π (v + 1)))
    (hpts : ∀ (v : ℕ) (g : G.Point (PadicAlgCl p) v),
        (∃ g' : B v →ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p,
            g'.comp (π v : G.level v →ₐ[PadicAlgCl.ringOfIntegers p K] B v) =
              PDivisibleGroup.Point.toAlgHom g) ↔
          ∃ x ∈ M, G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul g) =
            (x : ℕ → G.Points (PadicAlgCl p)) v) :
    ∃ m : ∀ j, B j →ₐc[PadicAlgCl.ringOfIntegers p K] B (j + 1),
      (∀ j, (m j).comp (t j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p) ∧
      (∀ j, (t j).comp (m j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B j) p) ∧
      (∀ j, ∀ d ∈ HopfAlgebra.hopfKer (t j),
        PDivisibleGroup.Hopf.nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p d =
          algebraMap (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) (Coalgebra.counit d)) ∧
      (∀ j, Set.MapsTo (m (j + 1)) (HopfAlgebra.hopfKer (t j) : Set (B (j + 1)))
        (HopfAlgebra.hopfKer (t (j + 1)) : Set (B (j + 2)))) ∧
      ∃ i₀ : ℕ, ∀ i, i₀ ≤ i →
        Set.BijOn (m (i + 1)) (HopfAlgebra.hopfKer (t i) : Set (B (i + 1)))
          (HopfAlgebra.hopfKer (t (i + 1)) : Set (B (i + 2))) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_exists_bialgHom_comp_eq_nsmulBialgHom_and_bijOn_hopfKer_of_hopf_quotient_system_of_ringOfIntegers.solution
