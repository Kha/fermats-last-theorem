module

public import Definitions.Def_ModularCurve_KroneckerTransport
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Polynomial

namespace ModularCurve

section FibrePoly

variable {k : Type*} [Field k]

def fibrePoly (Φ : Polynomial (Polynomial ℤ)) (a : k) : Polynomial k :=
  Φ.map (Polynomial.eval₂RingHom (Int.castRingHom k) a)

variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ]

theorem eval₂RingHom_intCast_eq_comp (a : k) :
    Polynomial.eval₂RingHom (Int.castRingHom k) a =
      (Polynomial.eval₂RingHom (ZMod.castHom (dvd_refl ℓ) k) a).comp
        (Polynomial.mapRingHom (Int.castRingHom (ZMod ℓ))) := by
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, RingHom.comp_apply,
    Polynomial.coe_mapRingHom, Polynomial.map_X, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X]

theorem fibrePoly_eq_map_reduceModBivar (Φ : Polynomial (Polynomial ℤ)) (a : k) :
    fibrePoly Φ a =
      (reduceModBivar ℓ Φ).map
        (Polynomial.eval₂RingHom (ZMod.castHom (dvd_refl ℓ) k) a) := by
  rw [fibrePoly, eval₂RingHom_intCast_eq_comp (ℓ := ℓ),
    show reduceModBivar ℓ Φ
      = Φ.map (Polynomial.mapRingHom (Int.castRingHom (ZMod ℓ))) from rfl,
    Polynomial.map_map]

end FibrePoly

section Factorization

variable {k : Type*} [Field k] {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ] [PerfectRing k ℓ]

theorem C_sub_X_pow_eq_neg_pow (a : k) :
    Polynomial.C a - Polynomial.X ^ ℓ =
      -((Polynomial.X - Polynomial.C ((frobeniusEquiv k ℓ).symm a)) ^ ℓ) := by
  have hpoly : (Polynomial.X - Polynomial.C ((frobeniusEquiv k ℓ).symm a)) ^ ℓ =
      Polynomial.X ^ ℓ - Polynomial.C ((frobeniusEquiv k ℓ).symm a) ^ ℓ :=
    sub_pow_expChar _ _
  rw [hpoly, ← Polynomial.C_pow, frobeniusEquiv_symm_pow_p, neg_sub]

end Factorization

end ModularCurve
