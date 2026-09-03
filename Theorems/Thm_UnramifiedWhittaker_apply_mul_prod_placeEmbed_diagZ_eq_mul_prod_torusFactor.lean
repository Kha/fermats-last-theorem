import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import P2M.Util
import P2M.Sol.S_UnramifiedWhittaker_apply_mul_prod_placeEmbed_diagZ_eq_mul_prod_torusFactor

set_option autoImplicit false

open Matrix
open IsDedekindDomain NumberField AdelicDock

theorem UnramifiedWhittaker.apply_mul_prod_placeEmbed_diagZ_eq_mul_prod_torusFactor
    {R : Type*} {K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K]
    (W : GL (Fin 2) (AdeleRing R K) → ℂ)
    (ψ : ∀ v : HeightOneSpectrum R, AddChar (v.adicCompletion K) ℂ)
    (ϖ : ∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K)
    (hπ : ∀ v : HeightOneSpectrum R,
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v) ≠ 0)
    (lam om : HeightOneSpectrum R → ℂ)
    {I : HeightOneSpectrum R → Type*} [∀ v, Fintype (I v)] [∀ v, Nonempty (I v)]
    (b : ∀ v : HeightOneSpectrum R, I v → v.adicCompletionIntegers K)
    (L : List (HeightOneSpectrum R)) (hL : L.Nodup)
    (hψ0 : ∀ v ∈ L, ∀ r : v.adicCompletionIntegers K,
      ψ v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) = 1)
    (hψ1 : ∀ v ∈ L, ∃ r : v.adicCompletionIntegers K,
      ψ v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r /
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v)) ≠ 1)
    (hN : ∀ v ∈ L, ∀ (x : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing R K)),
      W (placeEmbed K v (unipotent x) * g) = ψ v x * W g)
    (hK : ∀ v ∈ L, ∀ (r : v.adicCompletionIntegers K) (g : GL (Fin 2) (AdeleRing R K)),
      W (g * placeEmbed K v (unipotent
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r))) = W g)
    (hT : ∀ v ∈ L, ∀ g : GL (Fin 2) (AdeleRing R K),
      (∑ i, W (g * placeEmbed K v (repSome
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v)) (hπ v)
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (b v i))))) +
        W (g * placeEmbed K v (repInf
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v)) (hπ v))) =
        lam v * W g)
    (hZ : ∀ v ∈ L, ∀ g : GL (Fin 2) (AdeleRing R K),
      W (g * placeEmbed K v (scalarPi
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v)) (hπ v))) =
        om v * W g)
    (g₀ : GL (Fin 2) (AdeleRing R K))
    (hg₀ : ∀ v ∈ L, ∀ x : GL (Fin 2) (v.adicCompletion K),
      g₀ * placeEmbed K v x = placeEmbed K v x * g₀)
    (m : HeightOneSpectrum R → ℤ) :
    W (g₀ * (L.map fun v => placeEmbed K v (diagZ
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ v)) (hπ v) (m v))).prod) =
      W g₀ * (L.map fun v => torusFactor (Fintype.card (I v)) (lam v) (om v) (m v)).prod := by p2m_exact_reverting @_root_.P2MW.S_UnramifiedWhittaker_apply_mul_prod_placeEmbed_diagZ_eq_mul_prod_torusFactor.solution
