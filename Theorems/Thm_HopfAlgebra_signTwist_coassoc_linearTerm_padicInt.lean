import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_signTwist_coassoc_linearTerm_padicInt

open scoped TensorProduct
open scoped TensorProduct in
theorem HopfAlgebra.signTwist_coassoc_linearTerm_padicInt
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (d₀ : ℤ_[p]) (hd₀ : IsUnit d₀)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] H) :
    let Pm : H →ₗ[ℤ_[p]] H :=
      Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p])
    let Q := TensorProduct.map Pm Pm
    let Δ : H →ₗ[ℤ_[p]] H ⊗[ℤ_[p]] H := Coalgebra.comul
    let A := (TensorProduct.assoc ℤ_[p] H H H).toLinearMap
    ∀ a : H,
      A ((LinearMap.rTensor H (Q.comp Δ)) (Δ a)) + A ((LinearMap.rTensor H Δ) (Q (Δ a)))
      = (LinearMap.lTensor H (Q.comp Δ)) (Δ a) + (LinearMap.lTensor H Δ) (Q (Δ a)) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_signTwist_coassoc_linearTerm_padicInt.solution
