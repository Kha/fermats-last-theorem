import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_BaseChange
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_PadicAlgCl_RingOfIntegers
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_exists_linearEquiv_tateModule_baseChange_ringOfIntegers_of_ringHom_padicAlgCl

set_option autoImplicit false

theorem PDivisibleGroup.exists_linearEquiv_tateModule_baseChange_ringOfIntegers_of_ringHom_padicAlgCl
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] [Algebra O (PadicAlgCl.ringOfIntegers p K)]
    (ι : AlgebraicClosure ℚ →+* PadicAlgCl p)
    (hι : ∀ x : O, ((algebraMap O (PadicAlgCl.ringOfIntegers p K) x : PadicAlgCl.ringOfIntegers p K) : PadicAlgCl p) = ι (algebraMap O (AlgebraicClosure ℚ) x))
    (hιP : ∀ t : AlgebraicClosure ℚ, P.valuation t < 1 ↔ ‖ι t‖ < 1)
    (hιP' : ∀ t : AlgebraicClosure ℚ, t ∈ P ↔ ‖ι t‖ ≤ 1)
    {h : ℕ} (H : PDivisibleGroup O p h) :
    ∃ Θ : TateModule p (H.Points (AlgebraicClosure ℚ)) ≃ₗ[ℤ_[p]] TateModule p ((H.baseChange (PadicAlgCl.ringOfIntegers p K)).Points (PadicAlgCl p)),
      (∀ (τ' : AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ) (τl : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
        (∀ t : AlgebraicClosure ℚ, ι (τ' t) = τl (ι t)) →
        ∀ y : TateModule p (H.Points (AlgebraicClosure ℚ)),
          Θ (H.tateModuleRep (AlgebraicClosure ℚ) τ' y) = (H.baseChange (PadicAlgCl.ringOfIntegers p K)).tateModuleRep (PadicAlgCl p) τl (Θ y)) ∧
      (∀ y : TateModule p (H.Points (AlgebraicClosure ℚ)),
        (∀ n : ℕ, ∃ (w : ℕ) (g : H.Point (AlgebraicClosure ℚ) w),
      H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul g) =
        (y : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
      ∀ a : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom g a -
        algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
        ∀ n : ℕ, ∃ (w : ℕ) (g : (H.baseChange (PadicAlgCl.ringOfIntegers p K)).Point (PadicAlgCl p) w),
          (H.baseChange (PadicAlgCl.ringOfIntegers p K)).pointsMkAdd (PadicAlgCl p) w (Additive.ofMul g) =
            ((Θ y : TateModule p ((H.baseChange (PadicAlgCl.ringOfIntegers p K)).Points (PadicAlgCl p))) : ℕ → (H.baseChange (PadicAlgCl.ringOfIntegers p K)).Points (PadicAlgCl p)) n ∧
          ∀ a : (H.baseChange (PadicAlgCl.ringOfIntegers p K)).level w, ‖PDivisibleGroup.Point.toAlgHom g a -
            algebraMap (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p) (Coalgebra.counit a)‖ < 1) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_exists_linearEquiv_tateModule_baseChange_ringOfIntegers_of_ringHom_padicAlgCl.solution
