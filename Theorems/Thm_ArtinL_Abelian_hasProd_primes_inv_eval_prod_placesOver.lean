import Mathlib
import Definitions.Def_ArtinL_EulerFactor
import Definitions.Def_ArtinL_Abelian
import P2M.Util
import P2M.Sol.S_ArtinL_Abelian_hasProd_primes_inv_eval_prod_placesOver

set_option autoImplicit false

open scoped MatrixGroups
open NumberField

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
open scoped Classical in

theorem ArtinL.Abelian.hasProd_primes_inv_eval_prod_placesOver
    (K : Type) (M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes =>
        ((∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
            if ((p : ℕ) : 𝓞 K) ∈ v.asIdeal then
              (1 - Polynomial.C (ArtinL.Abelian.localValue ψ v) *
                Polynomial.X ^ (Ideal.span {((p : ℕ) : ℤ)}).inertiaDeg' v.asIdeal : Polynomial ℂ)
            else 1).eval ((p : ℂ) ^ (-s)))⁻¹)
      (ArtinL.Abelian.LSeries ψ s) := by p2m_exact_reverting @_root_.P2MW.S_ArtinL_Abelian_hasProd_primes_inv_eval_prod_placesOver.solution
