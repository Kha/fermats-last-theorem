import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.exists_equiv_of_span_singleton_eq
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π π₂ : 𝒪}
    (h : Ideal.span {π} = Ideal.span {π₂}) :
    ∃ Φ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], DeligneDatum (K := K) π B ≃ DeligneDatum (K := K) π₂ B,
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (d : DeligneDatum (K := K) π B), (Φ B d).line = d.line) ∧
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (g : Matrix.GeneralLinearGroup (Fin 2) K)
          (d d' : DeligneDatum (K := K) π B),
        DeligneDatum.IsPullback (K := K) (π := π₂) B g (Φ B d) (Φ B d') ↔
          DeligneDatum.IsPullback (K := K) (π := π) B g d d') ∧
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
          (d : DeligneDatum (K := K) π B) (d' : DeligneDatum (K := K) π B'),
        DeligneDatum.IsBaseChange (K := K) (π := π₂) f (Φ B d) (Φ B' d') ↔
          DeligneDatum.IsBaseChange (K := K) (π := π) f d d') := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.solution
