import Mathlib
import Definitions.Def_AutomorphicForm_FormalBaseChange
import P2M.Util
import P2M.Sol.S_AutomorphicForm_tsum_fibre_eq_const_mul_sum_tsum_fibre_formalBaseChange_of_forall_finset_record_of_subset

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open scoped BigOperators NumberField

theorem AutomorphicForm.tsum_fibre_eq_const_mul_sum_tsum_fibre_formalBaseChange_of_forall_finset_record_of_subset
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∈ SK → w ∈ SL)
    (hSsat : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (rec : ℕ → HeightOneSpectrum (𝓞 L)) (hrec : ∀ k, rec k ∉ SL)
    (hcov : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
      ∃ k, HeightOneSpectrum.under (𝓞 K) (rec k) = HeightOneSpectrum.under (𝓞 K) w)
    (CL : Set (HeckeEigensystem L ℂ)) (mL : HeckeEigensystem L ℂ → ℂ)
    (hmL : Summable fun Ψ : CL => ‖mL Ψ‖)
    (hL : ∀ Ψ ∈ CL, mL Ψ ≠ 0 → ∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (Ψ.a w, Ψ.b w) = (Ψ.a w', Ψ.b w'))
    {ΞT : Type} (Ξ : Finset ΞT) (CK : ΞT → Set (HeckeEigensystem K ℂ)) (mK : ΞT → HeckeEigensystem K ℂ → ℂ)
    (hmK : ∀ ξ ∈ Ξ, Summable fun π : CK ξ => ‖mK ξ π‖)
    (hK : ∀ ξ ∈ Ξ, ∀ π ∈ CK ξ, mK ξ π ≠ 0 → ∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' →
        ((formalBaseChange K L π).a w, (formalBaseChange K L π).b w) =
          ((formalBaseChange K L π).a w', (formalBaseChange K L π).b w'))
    (t : HeightOneSpectrum (𝓞 L) → ℂ × ℂ)
    (ht : ∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → t w = t w')
    (E : ℕ → (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (e : ℕ → ℂ) (he : Summable fun n => ‖e n‖)
    (hE : ∀ n, e n ≠ 0 →
      (∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
          HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → E n w = E n w') ∧
        ∃ w : HeightOneSpectrum (𝓞 L), w ∉ SL ∧ t w ≠ E n w)
    (bandL bandK c₀ : ℂ) (hbandL : bandL ≠ 0) (F₀ : Finset ℕ)
    (hlevel : ∀ F : Finset ℕ, F₀ ⊆ F →
      bandL * (∑' Ψ : {Ψ : HeckeEigensystem L ℂ // Ψ ∈ CL ∧ ∀ k ∈ F, (Ψ.a (rec k), Ψ.b (rec k)) = t (rec k)}, mL Ψ.1) -
        c₀ * bandK * (∑ ξ ∈ Ξ, ∑' π : {π : HeckeEigensystem K ℂ // π ∈ CK ξ ∧
            ∀ k ∈ F, ((formalBaseChange K L π).a (rec k), (formalBaseChange K L π).b (rec k)) = t (rec k)},
          mK ξ π.1) +
        (∑' n : {n : ℕ // ∀ k ∈ F, E n (rec k) = t (rec k)}, e n.1) = 0) :
    (∑' Ψ : {Ψ : HeckeEigensystem L ℂ // Ψ ∈ CL ∧
        ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL → (Ψ.a w, Ψ.b w) = t w}, mL Ψ.1) =
      c₀ * bandK / bandL * ∑ ξ ∈ Ξ, ∑' π : {π : HeckeEigensystem K ℂ // π ∈ CK ξ ∧
          ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
            ((formalBaseChange K L π).a w, (formalBaseChange K L π).b w) = t w}, mK ξ π.1 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_tsum_fibre_eq_const_mul_sum_tsum_fibre_formalBaseChange_of_forall_finset_record_of_subset.solution
