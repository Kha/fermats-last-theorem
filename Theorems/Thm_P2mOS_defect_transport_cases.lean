import Mathlib
import P2M.Util
import P2M.Sol.S_P2mOS_defect_transport_cases

set_option autoImplicit false

theorem P2mOS.defect_transport_cases
    {S : Type*} [CommRing S] {I : Type*} [LinearOrder I]
    (U U' : I → I → S) (hUU' : ∀ p q, p < q → U p q * U' p q = 1) (f : Fin 3 → I) :
    (¬ Function.Injective f →
      (if f 0 < f 1 then U (f 0) (f 1) else if f 0 = f 1 then 1 else U' (f 1) (f 0)) *
        (if f 1 < f 2 then U (f 1) (f 2) else if f 1 = f 2 then 1 else U' (f 2) (f 1)) *
        (if f 0 < f 2 then U' (f 0) (f 2) else if f 0 = f 2 then 1 else U (f 2) (f 0)) - 1 = 0) ∧
    (∀ σ : Equiv.Perm (Fin 3), StrictMono (f ∘ σ) →
      (U (f (σ 0)) (f (σ 1)) * U (f (σ 1)) (f (σ 2)) * U' (f (σ 0)) (f (σ 2)) - 1) *
        (U (f (σ 0)) (f (σ 1)) * U (f (σ 1)) (f (σ 2)) * U' (f (σ 0)) (f (σ 2)) - 1) = 0 →
      (if f 0 < f 1 then U (f 0) (f 1) else if f 0 = f 1 then 1 else U' (f 1) (f 0)) *
        (if f 1 < f 2 then U (f 1) (f 2) else if f 1 = f 2 then 1 else U' (f 2) (f 1)) *
        (if f 0 < f 2 then U' (f 0) (f 2) else if f 0 = f 2 then 1 else U (f 2) (f 0)) - 1 =
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ)) •
        (U (f (σ 0)) (f (σ 1)) * U (f (σ 1)) (f (σ 2)) * U' (f (σ 0)) (f (σ 2)) - 1)) := by p2m_exact_reverting @_root_.P2MW.S_P2mOS_defect_transport_cases.solution
