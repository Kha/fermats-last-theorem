import Definitions.Def_CerednikDrinfeld_Ribbon
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_ribbonKernel_unfold_eq_and_ribbonGram_eq_and_heckeKernelMap_eq

set_option autoImplicit false

open CerednikDrinfeld ModularCurve

theorem CerednikDrinfeld.ribbonKernel_unfold_eq_and_ribbonGram_eq_and_heckeKernelMap_eq
    {E V : Type} [Fintype E] [Fintype V] [DecidableEq V] (D : DegeneracyData E V) :
    let D' : DegeneracyData E (V × Fin 2) := ⟨fun e => (D.a e, 0), fun e => (D.b e, 1), D.w⟩
    ribbonKernel D' = ribbonKernel D ∧
    (∀ (x y : E → ℤ) (hx : x ∈ ribbonKernel D) (hy : y ∈ ribbonKernel D)
        (hx' : x ∈ ribbonKernel D') (hy' : y ∈ ribbonKernel D'),
      ribbonGram D' ⟨x, hx'⟩ ⟨y, hy'⟩ = ribbonGram D ⟨x, hx⟩ ⟨y, hy⟩) ∧
    (∀ (H : HeckeData D) (H' : HeckeData D'), (∀ ℓ : Nat.Primes, H'.T ℓ = H.T ℓ) →
      ∀ (ℓ : Nat.Primes) (x : E → ℤ) (hx : x ∈ ribbonKernel D) (hx' : x ∈ ribbonKernel D'),
        ((heckeKernelMap H' ℓ ⟨x, hx'⟩ : ↥(ribbonKernel D')) : E → ℤ) =
          ((heckeKernelMap H ℓ ⟨x, hx⟩ : ↥(ribbonKernel D)) : E → ℤ)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_ribbonKernel_unfold_eq_and_ribbonGram_eq_and_heckeKernelMap_eq.solution
