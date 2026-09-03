import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_signTwist_linearEquiv_padicInt_of_odd

open scoped NNReal
open scoped TensorProduct in
theorem HopfAlgebra.exists_signTwist_linearEquiv_padicInt_of_odd
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (d₀ : ℤ_[p]) (hd₀ : IsUnit d₀)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]
    (hfin : Module.Finite ℤ_[p] H) (hflat : Module.Flat ℤ_[p] H)
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] H) :
    let Pm : H →ₗ[ℤ_[p]] H :=
      Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p])
    ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra ℤ_[p] H'),
      Module.Finite ℤ_[p] H' ∧ Module.Flat ℤ_[p] H' ∧ Coalgebra.IsCocomm ℤ_[p] H' ∧
      ∃ e : H' ≃ₗ[ℤ_[p]] H,
        e 1 = 1 ∧
        (∀ a b : H', e (a * b) = e a * e b + (d₀ - 1) • (Pm (e a) * Pm (e b))) ∧
        (∀ a : H', (Coalgebra.counit (e a) : ℤ_[p]) = Coalgebra.counit a) ∧
        (∀ a : H', e (HopfAlgebra.antipode ℤ_[p] a) = HopfAlgebra.antipode ℤ_[p] (e a)) ∧
        (∀ a : H', (TensorProduct.map (e : H' →ₗ[ℤ_[p]] H) (e : H' →ₗ[ℤ_[p]] H))
                    (Coalgebra.comul a)
              = Coalgebra.comul (e a)
                + (Ring.inverse d₀ - 1) •
                    (TensorProduct.map Pm Pm) (Coalgebra.comul (e a))) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_signTwist_linearEquiv_padicInt_of_odd.solution
