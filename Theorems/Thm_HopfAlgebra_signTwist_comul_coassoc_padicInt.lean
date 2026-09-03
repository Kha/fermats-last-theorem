import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_signTwist_comul_coassoc_padicInt

open scoped TensorProduct
open scoped TensorProduct in
theorem HopfAlgebra.signTwist_comul_coassoc_padicInt
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (d₀ : ℤ_[p]) (hd₀ : IsUnit d₀)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] H) :
    let Pm : H →ₗ[ℤ_[p]] H :=
      Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p])
    let Δ' : H →ₗ[ℤ_[p]] (H ⊗[ℤ_[p]] H) :=
      Coalgebra.comul + (Ring.inverse d₀ - 1) • ((TensorProduct.map Pm Pm).comp Coalgebra.comul)
    ↑(TensorProduct.assoc ℤ_[p] H H H) ∘ₗ LinearMap.rTensor H Δ' ∘ₗ Δ'
      = LinearMap.lTensor H Δ' ∘ₗ Δ' := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_signTwist_comul_coassoc_padicInt.solution
