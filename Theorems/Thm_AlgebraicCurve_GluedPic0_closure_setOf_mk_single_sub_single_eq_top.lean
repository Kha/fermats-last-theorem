import Mathlib
import Definitions.Def_AlgebraicCurve_GluedPic0
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_GluedPic0_closure_setOf_mk_single_sub_single_eq_top

set_option autoImplicit false

theorem AlgebraicCurve.GluedPic0.closure_setOf_mk_single_sub_single_eq_top
    {K F : Type*} [Field K] [Field F] [Algebra K F] [AlgebraicCurve.HasPrincipalDivisors K F]
    (S : Finset (AlgebraicCurve.Place K F × AlgebraicCurve.Place K F))
    (hS : Set.InjOn Prod.snd (S : Set (AlgebraicCurve.Place K F × AlgebraicCurve.Place K F)))
    (hrat : ∀ v : AlgebraicCurve.Place K F, Function.Surjective (algebraMap K v.ResidueField))
    (hval : ∀ (E : Finset (AlgebraicCurve.Place K F)) (c : AlgebraicCurve.Place K F → Kˣ),
      ∃ g : F, ∀ e ∈ E, e.HasValue g (c e))
    (T₀ T₁ : Finset (AlgebraicCurve.Place K F)) :
    AddSubgroup.closure {ξ : AlgebraicCurve.GluedPic0 K F S |
      ∃ (i : Fin 2) (P Q : AlgebraicCurve.Place K F) (x : ↥(AlgebraicCurve.GluingData.admissible S)),
        P ∉ (if i = 0 then T₀ else T₁) ∧ Q ∉ (if i = 0 then T₀ else T₁) ∧
        (x : AlgebraicCurve.GluingData K F S).1 =
            (if i = 0 then Finsupp.single P 1 - Finsupp.single Q 1 else 0) ∧
        (x : AlgebraicCurve.GluingData K F S).2.1 =
            (if i = 1 then Finsupp.single P 1 - Finsupp.single Q 1 else 0) ∧
        (x : AlgebraicCurve.GluingData K F S).2.2 = 0 ∧
        ξ = AlgebraicCurve.GluedPic0.mk S x} = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_GluedPic0_closure_setOf_mk_single_sub_single_eq_top.solution
