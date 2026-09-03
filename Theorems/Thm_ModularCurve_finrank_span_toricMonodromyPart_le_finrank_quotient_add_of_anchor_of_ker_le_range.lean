import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ToricMonodromyPart
import Definitions.Def_ModularCurve_ComponentGroupHecke
import P2M.Util
import P2M.Sol.S_ModularCurve_finrank_span_toricMonodromyPart_le_finrank_quotient_add_of_anchor_of_ker_le_range

set_option autoImplicit false
open ModularCurve

theorem
    ModularCurve.finrank_span_toricMonodromyPart_le_finrank_quotient_add_of_anchor_of_ker_le_range
    (p : ℕ) [Fact p.Prime] {M : ℕ} [NeZero M] (r : ℕ) (hpr : p ≠ r)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    {ι₁ : Type} [Fintype ι₁]
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hpm : (p : HeckeAlg) ∈ 𝔪)
    (T₁ : Nat.Primes → Matrix ι₁ ι₁ ℤ)
    (n₁ : Nat.Primes → ℤ) (hcol₁ : ∀ ℓ : Nat.Primes, HeckeRowSums (T₁ ℓ).transpose (n₁ ℓ))
    (ε₁ : letI := heckeModuleBar M;
      ↥(toricMonodromyPart (J := JZero M) r (A.inertiaSubgroupIn ℚ)) ≃+
        (↥(characterLattice ι₁) →+ Additive (IsLocalRing.ResidueField A)ˣ))
    (hε₁ : letI := heckeModuleBar M;
      ∀ (ℓ : Nat.Primes) (y : ↥(toricMonodromyPart (J := JZero M) r (A.inertiaSubgroupIn ℚ)))
        (x : ↥(characterLattice ι₁)),
        ε₁ (heckeGen ℓ • y) x = ε₁ y (heckeCharacterAction (T₁ ℓ).transpose (hcol₁ ℓ) x))
    (Q : Type) [AddCommGroup Q] [Module HeckeAlg Q] [Module.Finite ℤ Q]
    (φ : Q →+ ↥(characterLattice ι₁))
    (hφT : ∀ (ℓ : Nat.Primes) (z : Q), φ (heckeGen ℓ • z) = heckeCharacterAction (T₁ ℓ).transpose (hcol₁ ℓ) (φ z))
    (L : Type) [AddCommGroup L] [Module HeckeAlg L] [Module.Finite ℤ L]
    (πL : ↥(characterLattice ι₁) →+ L) (hπsurj : Function.Surjective πL)
    (hπT : ∀ (ℓ : Nat.Primes) (x : ↥(characterLattice ι₁)),
      πL (heckeCharacterAction (T₁ ℓ).transpose (hcol₁ ℓ) x) = heckeGen ℓ • πL x)
    (hker : ∀ x : ↥(characterLattice ι₁), πL x = 0 → x ∈ AddMonoidHom.range φ) :
    letI := heckeModuleBar M
    Module.finrank (HeckeAlg ⧸ 𝔪)
        ↥(Submodule.span (HeckeAlg ⧸ 𝔪)
          ((Subtype.val : ↥(heckeTorsion (JZero M) 𝔪) → JZero M) ⁻¹'
            (toricMonodromyPart (J := JZero M) r (A.inertiaSubgroupIn ℚ) : Set (JZero M)))) ≤
      Module.finrank (HeckeAlg ⧸ 𝔪) (L ⧸ (𝔪 • (⊤ : Submodule HeckeAlg L))) +
        Module.finrank (HeckeAlg ⧸ 𝔪) (Q ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Q))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finrank_span_toricMonodromyPart_le_finrank_quotient_add_of_anchor_of_ker_le_range.solution
