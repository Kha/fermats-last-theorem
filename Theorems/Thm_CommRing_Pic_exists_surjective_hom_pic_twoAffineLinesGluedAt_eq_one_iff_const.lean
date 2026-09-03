import Mathlib
import P2M.Util
import P2M.Sol.S_CommRing_Pic_exists_surjective_hom_pic_twoAffineLinesGluedAt_eq_one_iff_const

open Polynomial

universe u v

theorem CommRing.Pic.exists_surjective_hom_pic_twoAffineLinesGluedAt_eq_one_iff_const
    {k : Type u} [Field k] {ι : Type v} [Finite ι] (a b : ι → k)
    (ha : Function.Injective a) (hb : Function.Injective b) :
    let R : Subalgebra k (k[X] × k[X]) :=
      AlgHom.equalizer
        (Pi.algHom k (fun _ : ι => k) fun i => (Polynomial.aeval (a i)).comp (AlgHom.fst k k[X] k[X]))
        (Pi.algHom k (fun _ : ι => k) fun i => (Polynomial.aeval (b i)).comp (AlgHom.snd k k[X] k[X]))
    ∃ δ : (ι → kˣ) →* CommRing.Pic ↥R,
      Function.Surjective δ ∧
      (∀ w : ι → kˣ, δ w = 1 ↔ ∃ c : kˣ, w = Function.const ι c) ∧
      ∀ w : ι → kˣ, ∃ N : Submodule ↥R (k[X] × k[X]),
        (∀ p : k[X] × k[X], p ∈ N ↔ ∀ i, (p.1).eval (a i) = (w i : k) * (p.2).eval (b i)) ∧
        Nonempty ((δ w : CommRing.Pic ↥R) ≃ₗ[↥R] ↥N) := by p2m_exact_reverting @_root_.P2MW.S_CommRing_Pic_exists_surjective_hom_pic_twoAffineLinesGluedAt_eq_one_iff_const.solution
