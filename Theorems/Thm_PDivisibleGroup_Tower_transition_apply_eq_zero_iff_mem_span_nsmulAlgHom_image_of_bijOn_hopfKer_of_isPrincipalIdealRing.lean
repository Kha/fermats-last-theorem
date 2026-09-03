import Mathlib
import Definitions.Def_PDivisibleGroup_Tower
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_Tower_transition_apply_eq_zero_iff_mem_span_nsmulAlgHom_image_of_bijOn_hopfKer_of_isPrincipalIdealRing
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.Tower.transition_apply_eq_zero_iff_mem_span_nsmulAlgHom_image_of_bijOn_hopfKer_of_isPrincipalIdealRing
    {R : Type} [CommRing R] [IsLocalRing R] [IsDomain R] [IsPrincipalIdealRing R] (p i₀ : ℕ)
    (B : ℕ → Type) [∀ w, CommRing (B w)] [∀ w, HopfAlgebra R (B w)]
    [∀ w, Coalgebra.IsCocomm R (B w)] [∀ w, Module.Finite R (B w)] [∀ w, Module.Free R (B w)]
    (t : ∀ w, B (w + 1) →ₐc[R] B w) (ht : ∀ w, Function.Surjective (t w))
    (m : ∀ w, B w →ₐc[R] B (w + 1))
    (hmt : ∀ w, (m w).comp (t w) = PDivisibleGroup.Hopf.nsmulBialgHom R (B (w + 1)) p)
    (htm : ∀ w, (t w).comp (m w) = PDivisibleGroup.Hopf.nsmulBialgHom R (B w) p)
    (hbij : ∀ w, i₀ ≤ w → Set.BijOn (m (w + 1)) (HopfAlgebra.hopfKer (t w) : Set (B (w + 1)))
      (HopfAlgebra.hopfKer (t (w + 1)) : Set (B (w + 2))))
    (v : ℕ) (x : B (i₀ + v + 1))
    (hx : x ∈ HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ (v + 1))) :
    t (i₀ + v) x = 0 ↔
      x ∈ Ideal.span (PDivisibleGroup.Hopf.nsmulAlgHom R (B (i₀ + v + 1)) (p ^ v) ''
        ((HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ (v + 1)) : Set (B (i₀ + v + 1))) ∩
          (PDivisibleGroup.Hopf.augIdeal R (B (i₀ + v + 1)) : Set (B (i₀ + v + 1))))) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_Tower_transition_apply_eq_zero_iff_mem_span_nsmulAlgHom_image_of_bijOn_hopfKer_of_isPrincipalIdealRing.solution
