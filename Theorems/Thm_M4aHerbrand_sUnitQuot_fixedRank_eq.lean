import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.GroupTheory.Perm.Cycle.Basic
import P2M.Util
import P2M.Sol.S_M4aHerbrand_sUnitQuot_fixedRank_eq
import Definitions.Def_Compat_Mathlib430
attribute [-simp] M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq

set_option autoImplicit false
open NumberField IsDedekindDomain

theorem M4aHerbrand.sUnitQuot_fixedRank_eq
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L)
    (S : Finset (HeightOneSpectrum (𝓞 K)))

    (W : Set (HeightOneSpectrum (𝓞 L))) (hW : W = {w | w.under (𝓞 K) ∈ ↑S})

    (Φ : ↥(W.unit L) ≃* ↥(W.unit L))
    (hΦ : ∀ u, (((Φ u : Lˣ) : L)) = σ (((u : Lˣ) : L)))

    (T : AddSubgroup (Additive ↥(W.unit L)))
    (hT : ∀ x, x ∈ T ↔ ∃ n : ℕ, n ≠ 0 ∧ n • x = 0)

    (ψ : AddAut (Additive ↥(W.unit L) ⧸ T))
    (hψ : ∀ u, ψ (QuotientAddGroup.mk (Additive.ofMul u))
          = QuotientAddGroup.mk (Additive.ofMul (Φ u)))

    (π : Equiv.Perm ↥W)
    (hπ : ∀ w, (π w).1.asIdeal = Ideal.map ((galRestrict (𝓞 K) K L (𝓞 L)) σ) w.1.asIdeal)
    (πl : AddAut (↥W → ℤ)) (hπl : ∀ f w, πl f w = f (π.symm w))

    (ρ : Equiv.Perm (InfinitePlace L)) (hρ : ∀ v, ρ v = v.comap (σ.symm : L →+* L))
    (ρl : AddAut (InfinitePlace L → ℤ)) (hρl : ∀ f v, ρl f v = f (ρ.symm v)) :
    ∀ e : ℕ,
      Module.finrank ℤ ↥(LinearMap.ker (((ψ ^ e) : AddAut _).toAddMonoidHom.toIntLinearMap - LinearMap.id)) + 1
        = Module.finrank ℤ ↥(LinearMap.ker (((πl ^ e) : AddAut _).toAddMonoidHom.toIntLinearMap - LinearMap.id))
          + Module.finrank ℤ ↥(LinearMap.ker (((ρl ^ e) : AddAut _).toAddMonoidHom.toIntLinearMap - LinearMap.id)) := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_sUnitQuot_fixedRank_eq.solution
