import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_intermediateField_finiteDimensional_henselianLocalRing_comap_of_henselianLocalRing

set_option autoImplicit false

universe u

theorem ValuationSubring.exists_intermediateField_finiteDimensional_henselianLocalRing_comap_of_henselianLocalRing
    {L : Type u} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (A₀ : Type u) [CommRing A₀] [IsNoetherianRing A₀] [HenselianLocalRing A₀] [IsDomain A₀]
    (hdim : Ring.KrullDimLE 1 A₀)
    (ι : A₀ →+* A) [IsLocalHom ι] (hι : Function.Injective ι)
    (K₀ : Subfield L)
    (hrange : Set.range (fun a : A₀ => ((ι a : A) : L)) = (A : Set L) ∩ (K₀ : Set L))
    [Algebra.IsAlgebraic K₀ L]
    (hres : Function.Surjective ((IsLocalRing.residue A).comp ι))
    (Λ : Finset L) :
    ∃ (K₁ : IntermediateField K₀ L) (_ : FiniteDimensional K₀ K₁),
      (↑Λ : Set L) ⊆ (K₁ : Set L) ∧
      ∃ (_ : IsNoetherianRing ↥(A.comap (algebraMap K₁ L)))
        (_ : HenselianLocalRing ↥(A.comap (algebraMap K₁ L)))
        (j : A₀ →+* ↥(A.comap (algebraMap K₁ L))) (ι₁ : ↥(A.comap (algebraMap K₁ L)) →+* A)
        (_ : IsLocalHom j) (_ : IsLocalHom ι₁),
        Function.Injective ι₁ ∧ ι₁.comp j = ι ∧
        Function.Surjective ((IsLocalRing.residue A).comp ι₁) ∧
        (∀ x : ↥(A.comap (algebraMap K₁ L)), ((ι₁ x : A) : L) = algebraMap K₁ L (x : K₁)) ∧
        (A ≠ ⊤ → IsDiscreteValuationRing ↥(A.comap (algebraMap K₁ L))) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_intermediateField_finiteDimensional_henselianLocalRing_comap_of_henselianLocalRing.solution
