import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_signTwist_withConv_mulEquiv_of_linearEquiv_padicInt

open scoped NNReal
open scoped TensorProduct in
theorem HopfAlgebra.exists_signTwist_withConv_mulEquiv_of_linearEquiv_padicInt
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (d : ℚ_[p]) (hd : ‖d‖₊ = 1) (hd_nsq : ¬ IsSquare d)
    (s : AlgebraicClosure ℚ_[p]) (hs : s ^ 2 = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) d)
    (d₀ : ℤ_[p]) (hd₀d : (d₀ : ℚ_[p]) = d) (hd₀ : IsUnit d₀)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]
    (hfin : Module.Finite ℤ_[p] H) (hflat : Module.Flat ℤ_[p] H)
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] H)
    (H' : Type) [CommRing H'] [HopfAlgebra ℤ_[p] H']
    (hfin' : Module.Finite ℤ_[p] H') (hflat' : Module.Flat ℤ_[p] H')
    (hcocomm' : Coalgebra.IsCocomm ℤ_[p] H')
    (e : H' ≃ₗ[ℤ_[p]] H)
    (he1 : e 1 = 1)
    (hemul : let Pm : H →ₗ[ℤ_[p]] H :=
        Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p])
      ∀ a b : H', e (a * b) = e a * e b + (d₀ - 1) • (Pm (e a) * Pm (e b)))
    (hecounit : ∀ a : H', (Coalgebra.counit (e a) : ℤ_[p]) = Coalgebra.counit a)
    (heant : ∀ a : H', e (HopfAlgebra.antipode ℤ_[p] a) = HopfAlgebra.antipode ℤ_[p] (e a))
    (hecomul : let Pm : H →ₗ[ℤ_[p]] H :=
        Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p])
      ∀ a : H', (TensorProduct.map (e : H' →ₗ[ℤ_[p]] H) (e : H' →ₗ[ℤ_[p]] H))
                  (Coalgebra.comul a)
            = Coalgebra.comul (e a)
              + (Ring.inverse d₀ - 1) •
                  (TensorProduct.map Pm Pm) (Coalgebra.comul (e a))) :
    ∃ β : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃
          WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]),
      (∀ f' g', β (f' * g') = β f' * β g') ∧
      ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
        (f' g' : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]))
        (g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
        (∀ h' : H', g' h' = σ (f' h')) →
        (∀ h : H, g h = σ ((β f') h)) →
          (σ s = s → β g' = g) ∧ (σ s ≠ s → β g' * g = 1) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_signTwist_withConv_mulEquiv_of_linearEquiv_padicInt.solution
