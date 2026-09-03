import Mathlib
import P2M.Util
import P2M.Sol.S_Subalgebra_exists_ringEquiv_localizationAtPrime_of_forall_mem_iff_exists_mul_eq

set_option autoImplicit false

open IsLocalRing

theorem Subalgebra.exists_ringEquiv_localizationAtPrime_of_forall_mem_iff_exists_mul_eq
    {A : Type*} {K : Type*} [CommRing A] [Field K] [Algebra A K]
    (R : Subalgebra A K) (P : Ideal ↥R) (hP : P.IsMaximal) (O : Subring K)
    (hO : ∀ f : K, f ∈ O ↔ ∃ g h : ↥R, h ∉ P ∧ f * (h : K) = (g : K)) :
    ∃ (hRO : ∀ r : ↥R, (r : K) ∈ O)
      (e : Localization.AtPrime P ≃+* ↥O),
      (∀ r : ↥R, e (algebraMap ↥R (Localization.AtPrime P) r) = ⟨(r : K), hRO r⟩) ∧
      ∃ _ : IsLocalRing ↥O,
        (∀ (f : K) (hf : f ∈ O), (⟨f, hf⟩ : ↥O) ∈ maximalIdeal ↥O ↔
            ∃ g h : ↥R, g ∈ P ∧ h ∉ P ∧ f * (h : K) = (g : K)) ∧
        (∀ r : ↥R, (⟨(r : K), hRO r⟩ : ↥O) ∈ maximalIdeal ↥O ↔ r ∈ P) ∧
        (IsNoetherianRing ↥R → IsNoetherianRing ↥O) ∧
        ((∀ r : ↥R, ∃ a : A, r - algebraMap A ↥R a ∈ P) →
          ∀ (f : K) (hf : f ∈ O), ∃ (a : A) (ha : algebraMap A K a ∈ O),
            ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨algebraMap A K a, ha⟩)) := by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_exists_ringEquiv_localizationAtPrime_of_forall_mem_iff_exists_mul_eq.solution
