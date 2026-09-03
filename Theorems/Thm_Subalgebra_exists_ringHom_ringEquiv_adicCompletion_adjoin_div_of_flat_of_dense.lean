import Mathlib
import P2M.Util
import P2M.Sol.S_Subalgebra_exists_ringHom_ringEquiv_adicCompletion_adjoin_div_of_flat_of_dense

set_option autoImplicit false

open IsLocalRing

theorem Subalgebra.exists_ringHom_ringEquiv_adicCompletion_adjoin_div_of_flat_of_dense
    {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    (C : Subalgebra A K) (y : Ideal ↥C) (hy : y.IsMaximal) (J : Ideal ↥C)
    (a : ↥C) (haJ : a ∈ J) (ha0 : ((a : ↥C) : K) ≠ 0)
    (Ba : Subalgebra A K)
    (hBa : Ba = (Algebra.adjoin ↥C {x : K | ∃ i ∈ J, x * ((a : ↥C) : K) = ((i : ↥C) : K)}).restrictScalars A)
    (P : Ideal ↥Ba) (hP : P.IsMaximal)
    (hPy : ∀ (b : ↥C) (hb : ((b : ↥C) : K) ∈ Ba), (⟨_, hb⟩ : ↥Ba) ∈ P ↔ b ∈ y)
    (S : Type*) [CommRing S] (Ψ : ↥C →+* S)
    (hflat : letI : Algebra ↥C S := Ψ.toAlgebra; Module.Flat ↥C S)
    (𝔫 : Ideal S) (h𝔫 : Ideal.map Ψ y = 𝔫)
    (hdense : ∀ (n : ℕ) (s : S), ∃ c : ↥C, Ψ c - s ∈ 𝔫 ^ n)
    (hcomap : ∀ n : ℕ, Ideal.comap Ψ (𝔫 ^ n) = y ^ n)
    (𝔐 : Ideal S) (h𝔐 : Ideal.map Ψ J = 𝔐) :
    let La := Localization.Away (Ψ a)
    let R : Subring La := Subring.closure
      (Set.range (algebraMap S La) ∪ {x : La | ∃ i ∈ 𝔐, x * algebraMap S La (Ψ a) = algebraMap S La i})
    Ψ a ∈ nonZeroDivisors S ∧ Ψ a ∈ 𝔐 ∧
    ∃ (Φ : ↥Ba →+* La) (hΦR : ∀ b : ↥Ba, Φ b ∈ R),
      (∀ (c : ↥C) (hc : ((c : ↥C) : K) ∈ Ba), Φ ⟨_, hc⟩ = algebraMap S La (Ψ c)) ∧
      (∀ (x : K) (hx : x ∈ Ba) (i : ↥C), i ∈ J → x * ((a : ↥C) : K) = ((i : ↥C) : K) →
        Φ ⟨x, hx⟩ * algebraMap S La (Ψ a) = algebraMap S La (Ψ i)) ∧
      ∃ (P' : Ideal ↥R) (_ : P'.IsMaximal),
        (∀ b : ↥Ba, (⟨Φ b, hΦR b⟩ : ↥R) ∈ P' ↔ b ∈ P) ∧
        (∀ (s : S) (hs : algebraMap S La s ∈ R), s ∈ 𝔫 → (⟨algebraMap S La s, hs⟩ : ↥R) ∈ P') ∧
        ∃ T : AdicCompletion P ↥Ba ≃+* AdicCompletion P' ↥R,
          ∀ b : ↥Ba, T (algebraMap ↥Ba (AdicCompletion P ↥Ba) b) =
            algebraMap ↥R (AdicCompletion P' ↥R) ⟨Φ b, hΦR b⟩ := by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_exists_ringHom_ringEquiv_adicCompletion_adjoin_div_of_flat_of_dense.solution
