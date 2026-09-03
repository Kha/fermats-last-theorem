import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk_of_ker_eq_torsionIdeal
attribute [-simp] HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul

universe u v

theorem PDivisibleGroup.exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk_of_ker_eq_torsionIdeal
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (h : ℕ)
    (L : ℕ → Type v) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra R (L v)]
    [∀ v, Coalgebra.IsCocomm R (L v)] [∀ v, Module.Free R (L v)] [∀ v, Module.Finite R (L v)]
    (t : ∀ v, L (v + 1) →ₐc[R] L v) (ht : ∀ v, Function.Surjective (t v))
    (hrankL : ∀ v, Module.finrank R (L v) = p ^ (v * h))
    (hkerL : ∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal R (L (v + 1)) (p ^ v))
    (v : ℕ) :
    (∃ e : L v ≃ₐ[R] ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + 1)) p).range,
        ∀ a : L (v + 1),
          ((e (t v a) : ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + 1)) p).range) : L (v + 1)) =
            PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + 1)) p a) ∧
      Module.Finite ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + 1)) p).range (L (v + 1)) ∧
      Module.Projective ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + 1)) p).range (L (v + 1)) ∧
      (∃ r : L (v + 1) →ₗ[↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + 1)) p).range]
          ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + 1)) p).range,
        ∀ c : ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + 1)) p).range, r (c : L (v + 1)) = c) ∧
      ∀ 𝔮 : PrimeSpectrum ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + 1)) p).range,
        Module.rankAtStalk (R := ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + 1)) p).range)
          (L (v + 1)) 𝔮 = p ^ h := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk_of_ker_eq_torsionIdeal.solution
