import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import P2M.Util
import P2M.Sol.S_UnramifiedWhittaker_mul_mul_apply_mul_placeEmbed_diagZ_mul_scalarPi_zpow_eq_of_torus_data_rat

set_option autoImplicit false

open Matrix
p2m_open "IsDedekindDomain NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm UnramifiedWhittaker~apply_mul_placeEmbed_diagZ_eq_mul_torusFactor"

theorem UnramifiedWhittaker.mul_mul_apply_mul_placeEmbed_diagZ_mul_scalarPi_zpow_eq_of_torus_data_rat
    (v : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    {I : Type*} [Fintype I] [Nonempty I] (b : I → v.adicCompletionIntegers ℚ)
    (hI : Fintype.card I = Ideal.absNorm v.asIdeal)
    (W W' F : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) → ℂ) (ψ ψ' : AddChar (v.adicCompletion ℚ) ℂ) (lam om lam' om' : ℂ)
    (hψ0 : ∀ r : v.adicCompletionIntegers ℚ, ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1)
    (hψ1 : ∃ r : v.adicCompletionIntegers ℚ,
      ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
        algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) ≠ 1)
    (hψ'0 : ∀ r : v.adicCompletionIntegers ℚ, ψ' (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1)
    (hψ'1 : ∃ r : v.adicCompletionIntegers ℚ,
      ψ' (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
        algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) ≠ 1)
    (hN : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)), W (placeEmbed ℚ v (unipotent x) * g) = ψ x * W g)
    (hN' : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)), W' (placeEmbed ℚ v (unipotent x) * g) = ψ' x * W' g)
    (hK : ∀ (r : v.adicCompletionIntegers ℚ) (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)),
      W (g * placeEmbed ℚ v (unipotent (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r))) = W g)
    (hK' : ∀ (r : v.adicCompletionIntegers ℚ) (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)),
      W' (g * placeEmbed ℚ v (unipotent (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r))) = W' g)
    (hT : ∀ g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ),
      (∑ i, W (g * placeEmbed ℚ v (repSome (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ
          (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (b i))))) +
        W (g * placeEmbed ℚ v (repInf (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) = lam * W g)
    (hT' : ∀ g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ),
      (∑ i, W' (g * placeEmbed ℚ v (repSome (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ
          (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (b i))))) +
        W' (g * placeEmbed ℚ v (repInf (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) = lam' * W' g)
    (hZ : ∀ g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ),
      W (g * placeEmbed ℚ v (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) = om * W g)
    (hZ' : ∀ g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ),
      W' (g * placeEmbed ℚ v (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) = om' * W' g)
    (hom : om ≠ 0) (hom' : om' ≠ 0)
    (hF : ∀ (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) (m n : ℤ), localAt ℚ v g = 1 →
      F (g * placeEmbed ℚ v
          (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m *
            scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n)) =
        (if 0 ≤ n then F g else 0)) :
    ∀ (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) (m n : ℤ), localAt ℚ v g = 1 →
      W (g * placeEmbed ℚ v
            (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m *
              scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n)) *
        (W' (g * placeEmbed ℚ v
            (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m *
              scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n)) *
          F (g * placeEmbed ℚ v
            (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m *
              scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n))) =
      (if 0 ≤ m ∧ 0 ≤ n then
          (om * om') ^ n.toNat *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) lam om m.toNat *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) lam' om' m.toNat
        else 0) * (W g * (W' g * F g)) := by p2m_exact_reverting @_root_.P2MW.S_UnramifiedWhittaker_mul_mul_apply_mul_placeEmbed_diagZ_mul_scalarPi_zpow_eq_of_torus_data_rat.solution
