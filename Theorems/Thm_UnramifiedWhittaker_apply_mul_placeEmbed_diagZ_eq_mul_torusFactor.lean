import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import P2M.Util
import P2M.Sol.S_UnramifiedWhittaker_apply_mul_placeEmbed_diagZ_eq_mul_torusFactor

set_option autoImplicit false

open Matrix
open IsDedekindDomain NumberField AdelicDock

theorem UnramifiedWhittaker.apply_mul_placeEmbed_diagZ_eq_mul_torusFactor
    {R : Type*} {K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R)
    {W : GL (Fin 2) (AdeleRing R K) → ℂ} {ψ : AddChar (v.adicCompletion K) ℂ}
    {ϖ : v.adicCompletionIntegers K}
    (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0) {lam om : ℂ}
    {I : Type*} [Fintype I] [Nonempty I] (b : I → v.adicCompletionIntegers K)
    (hψ0 : ∀ r : v.adicCompletionIntegers K,
      ψ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) = 1)
    (hψ1 : ∃ r : v.adicCompletionIntegers K,
      ψ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r /
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) ≠ 1)
    (hN : ∀ (x : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing R K)),
      W (placeEmbed K v (unipotent x) * g) = ψ x * W g)
    (hK : ∀ (r : v.adicCompletionIntegers K) (g : GL (Fin 2) (AdeleRing R K)),
      W (g * placeEmbed K v (unipotent
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r))) = W g)
    (hT : ∀ g : GL (Fin 2) (AdeleRing R K),
      (∑ i, W (g * placeEmbed K v (repSome
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (b i))))) +
        W (g * placeEmbed K v (repInf
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = lam * W g)
    (hZ : ∀ g : GL (Fin 2) (AdeleRing R K),
      W (g * placeEmbed K v (scalarPi
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = om * W g)
    {g₀ : GL (Fin 2) (AdeleRing R K)}
    (hg₀ : ∀ x : GL (Fin 2) (v.adicCompletion K), g₀ * placeEmbed K v x = placeEmbed K v x * g₀)
    (m : ℤ) :
    W (g₀ * placeEmbed K v (diagZ
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ m)) =
      W g₀ * torusFactor (Fintype.card I) lam om m := by p2m_exact_reverting @_root_.P2MW.S_UnramifiedWhittaker_apply_mul_placeEmbed_diagZ_eq_mul_torusFactor.solution
