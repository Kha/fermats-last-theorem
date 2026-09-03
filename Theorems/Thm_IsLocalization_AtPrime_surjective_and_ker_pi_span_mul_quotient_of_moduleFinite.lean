import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalization_AtPrime_surjective_and_ker_pi_span_mul_quotient_of_moduleFinite

set_option autoImplicit false

universe u

open scoped Pointwise

theorem IsLocalization.AtPrime.surjective_and_ker_pi_span_mul_quotient_of_moduleFinite
    (k : Type u) [Field k] {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Algebra k A]
    (K : Type u) [Field K] [Algebra k K] [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K]
    (hdim : ∀ p : Ideal A, p.IsPrime → p ≠ ⊥ → p.IsMaximal)
    (hres : ∀ m : Ideal A, m.IsMaximal → Function.Surjective (algebraMap k (A ⧸ m)))
    {X : Type u} (P : X → Prop) (R : X → Type u) [∀ z, CommRing (R z)] [∀ z, Algebra (R z) K]
    [∀ z : {z : X // P z}, Algebra A (R z.1)] [∀ z : {z : X // P z}, IsScalarTower A (R z.1) K]
    (𝔪 : {z : X // P z} → Ideal A) [∀ z, (𝔪 z).IsMaximal] (h𝔪 : Function.Injective 𝔪)
    [∀ z : {z : X // P z}, IsLocalization.AtPrime (R z.1) (𝔪 z)]
    (B : Subalgebra A K) (hB : Module.Finite A B) :

    let Bz : X → Submodule k K := fun z =>
      Submodule.span k ((B : Set K) * Set.range (algebraMap (R z) K))
    let Q : X → Type u := fun z =>
      ↥(Bz z) ⧸ (Submodule.span k (Set.range (algebraMap (R z) K))).comap (Bz z).subtype

    let φ : ↥(Submodule.span k (B : Set K)) →ₗ[k] ((z : {z : X // P z}) → Q z.1) :=
      LinearMap.pi fun z => (Submodule.mkQ _).comp (Submodule.inclusion (Submodule.span_mono
        (fun b hb => Set.mem_mul.mpr ⟨b, hb, 1, ⟨1, map_one _⟩, mul_one b⟩)))
    Function.Surjective φ ∧
      LinearMap.ker φ = (⨅ z : {z : X // P z}, Submodule.span k (Set.range (algebraMap (R z.1) K))).comap
        (Submodule.span k (B : Set K)).subtype ∧
      {z : {z : X // P z} | Nontrivial (Q z.1)}.Finite ∧
      ∀ z : {z : X // P z}, FiniteDimensional k (Q z.1) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalization_AtPrime_surjective_and_ker_pi_span_mul_quotient_of_moduleFinite.solution
