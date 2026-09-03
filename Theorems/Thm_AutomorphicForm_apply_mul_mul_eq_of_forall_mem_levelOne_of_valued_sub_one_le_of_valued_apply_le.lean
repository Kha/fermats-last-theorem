import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import P2M.Util
import P2M.Sol.S_AutomorphicForm_apply_mul_mul_eq_of_forall_mem_levelOne_of_valued_sub_one_le_of_valued_apply_le

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.apply_mul_mul_eq_of_forall_mem_levelOne_of_valued_sub_one_le_of_valued_apply_le
    (K : Type) [Field K] [NumberField K] (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S)
    (y₀ : AdelicGL2 (𝓞 K) K → ℂ)
    (hy₀lev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, y₀ (g * k) = y₀ g)
    (a : AdelicGL2 (𝓞 K) K) (c : ℕ)
    (ha : ∀ v ∈ S, ∀ i j : Fin 2,
      Valued.v ((((a : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
        ((Multiplicative.ofAdd (c : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ∧
      Valued.v (((((a⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
        ((Multiplicative.ofAdd (c : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (e : ℕ) (he : ∀ v ∈ S, (Associates.mk v.asIdeal).count (Associates.mk N).factors ≤ e)
    (nb : ℕ) (hnb : e + 2 * c ≤ nb) :
    ∀ (g k : AdelicGL2 (𝓞 K) K), k ∈ finiteAdelicGL2Subgroup K →
      glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → finComponent (𝓞 K) K v (glFin (𝓞 K) K k) = 1) →
      (∀ v ∈ S, ∀ i j : Fin 2,
        Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
            (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
          ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
      y₀ (g * k * a) = y₀ (g * a) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_apply_mul_mul_eq_of_forall_mem_levelOne_of_valued_sub_one_le_of_valued_apply_le.solution
