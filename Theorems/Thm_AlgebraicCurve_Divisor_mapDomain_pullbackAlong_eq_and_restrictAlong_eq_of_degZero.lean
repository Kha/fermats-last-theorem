import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_mapDomain_pullbackAlong_eq_and_restrictAlong_eq_of_degZero

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.mapDomain_pullbackAlong_eq_and_restrictAlong_eq_of_degZero
    {K F₁ F₂ : Type*} [Field K] [Field F₁] [Field F₂] [Algebra K F₁] [Algebra K F₂]
    {k C₁ C₂ : Type*} [Field k] [Field C₁] [Field C₂] [Algebra k C₁] [Algebra k C₂]
    [HasPrincipalDivisors K F₂] [HasPrincipalDivisors k C₂]
    (φ : F₁ →ₐ[K] F₂) (hφ : φ.toRingHom.IsIntegral)
    (φb : C₁ →ₐ[k] C₂) (hφb : φb.toRingHom.IsIntegral)
    (r₁ : Place K F₁ → Place k C₁) (r : Place K F₂ → Place k C₂)
    (h1F₁ : ∀ v : Place K F₁, v.deg = 1) (h1F₂ : ∀ W : Place K F₂, W.deg = 1)
    (h1C₁ : ∀ Q : Place k C₁, Q.deg = 1) (h1C₂ : ∀ Y : Place k C₂, Y.deg = 1)
    (hcompat : ∀ D : Divisor K F₁, D ∈ Divisor.degZero (K := K) (F := F₁) →
      Finsupp.mapDomain r (Divisor.pullbackAlong φ hφ D) =
        Divisor.pullbackAlong φb hφb (Finsupp.mapDomain r₁ D))
    (hdeg : ∀ v : Place K F₁,
      Divisor.degree (Divisor.pullbackAlong φ hφ (Finsupp.single v 1)) ≤
        Divisor.degree (Divisor.pullbackAlong φb hφb (Finsupp.single (r₁ v) 1)))
    (hnc : ∀ v : Place K F₁, ∃ v' : Place K F₁, r₁ v' ≠ r₁ v) :
    (∀ D : Divisor K F₁, Finsupp.mapDomain r (Divisor.pullbackAlong φ hφ D) =
        Divisor.pullbackAlong φb hφb (Finsupp.mapDomain r₁ D)) ∧
    (∀ W : Place K F₂, (r W).restrictAlong φb hφb = r₁ (W.restrictAlong φ hφ)) ∧
    (∀ D : Divisor K F₂, Finsupp.mapDomain r₁ (Divisor.pushforwardAlong φ hφ D) =
        Divisor.pushforwardAlong φb hφb (Finsupp.mapDomain r D)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_mapDomain_pullbackAlong_eq_and_restrictAlong_eq_of_degZero.solution
