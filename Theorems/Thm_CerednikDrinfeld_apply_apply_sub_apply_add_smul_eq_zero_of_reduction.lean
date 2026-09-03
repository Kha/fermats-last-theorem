import Mathlib
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_apply_apply_sub_apply_add_smul_eq_zero_of_reduction

set_option autoImplicit false

theorem CerednikDrinfeld.apply_apply_sub_apply_add_smul_eq_zero_of_reduction
    {J P : Type*} [AddCommGroup J] [AddCommGroup P]
    (D : AddSubgroup J) (g T : J → J) (hg : ∀ t ∈ D, g t ∈ D) (hT : ∀ t ∈ D, T t ∈ D)
    (red : J → P) (hadd : ∀ x ∈ D, ∀ y ∈ D, red (x + y) = red x + red y)
    (hinj : ∀ x ∈ D, red x = 0 → x = 0)
    (F V : P →+ P) (ℓ : ℕ)
    (hgal : ∀ t ∈ D, red (g t) = F (red t))
    (hhecke : ∀ t ∈ D, red (T t) = F (red t) + V (red t))
    (hVF : ∀ t ∈ D, V (F (red t)) = ℓ • red t) :
    ∀ t ∈ D, g (g t) - T (g t) + ℓ • t = 0 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_apply_apply_sub_apply_add_smul_eq_zero_of_reduction.solution
