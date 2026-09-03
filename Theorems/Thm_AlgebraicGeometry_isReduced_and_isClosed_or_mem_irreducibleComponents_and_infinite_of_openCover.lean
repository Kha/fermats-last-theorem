import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isReduced_and_isClosed_or_mem_irreducibleComponents_and_infinite_of_openCover

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isReduced_and_isClosed_or_mem_irreducibleComponents_and_infinite_of_openCover
    (X : Scheme.{u}) [JacobsonSpace X]
    (ι : Type u) (R : ι → Type u) [∀ i, CommRing (R i)]
    (g : ∀ i, Spec (CommRingCat.of (R i)) ⟶ X) (hg : ∀ i, IsOpenImmersion (g i))
    (hcov : ∀ x : X, ∃ i, x ∈ Set.range (g i).base)
    (hred : ∀ i, _root_.IsReduced (R i))
    (hdim : ∀ i (p : Ideal (R i)), p.IsPrime → p.IsMaximal ∨ p ∈ minimalPrimes (R i))
    (hinf : ∀ i (p : Ideal (R i)), p ∈ minimalPrimes (R i) → Set.Infinite {q : PrimeSpectrum (R i) | p ≤ q.asIdeal}) :
    IsReduced X ∧
      (∀ z : X, IsClosed ({z} : Set X) ∨ closure ({z} : Set X) ∈ irreducibleComponents X) ∧
      (∀ C ∈ irreducibleComponents X, Set.Infinite C) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isReduced_and_isClosed_or_mem_irreducibleComponents_and_infinite_of_openCover.solution
