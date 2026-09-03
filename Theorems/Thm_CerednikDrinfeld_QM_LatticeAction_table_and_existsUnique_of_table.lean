import Definitions.Def_CerednikDrinfeld_QMLatticeAction
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_QuaternionAlgebra_Order
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_LatticeAction_table_and_existsUnique_of_table

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

universe u

theorem CerednikDrinfeld.QM.LatticeAction.table_and_existsUnique_of_table
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    (c : Fin (2 * 2) → Fin (2 * 2) → Fin (2 * 2) → ℤ)
    (hc : ∀ j k : Fin (2 * 2), (β j : ℍ[ℚ, a, b]) * (β k : ℍ[ℚ, a, b]) = ∑ l, c j k l • (β l : ℍ[ℚ, a, b]))
    (u : Fin (2 * 2) → ℤ) (hu : (1 : ℍ[ℚ, a, b]) = ∑ l, u l • (β l : ℍ[ℚ, a, b]))
    {S' : Type u} [CommRing S'] {A' : Scheme.{u}} (f' : A' ⟶ Spec (CommRingCat.of S')) (L' : RelativeGroupLaw S' f')
    (hc' : L'.IsCommutative) :
    (∀ i' : LatticeAction Λ f' L',
        letI := L'.pointCommGroup hc' f'
        (∀ j k : Fin (2 * 2),
            (∏ l, (⟨i'.act (β l), i'.act_over (β l)⟩ : SchemeHomOver f' f') ^ (c j k l)) =
              ⟨i'.act (β k) ≫ i'.act (β j), by rw [Category.assoc, i'.act_over, i'.act_over]⟩) ∧
        (∏ l, (⟨i'.act (β l), i'.act_over (β l)⟩ : SchemeHomOver f' f') ^ (u l)) = ⟨𝟙 A', Category.id_comp _⟩) ∧
    (∀ (e : Fin (2 * 2) → (A' ⟶ A')) (he : ∀ j, e j ≫ f' = f')
        (hhom : ∀ (j : Fin (2 * 2)) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t f'),
          pushPt (e j) (he j) (L'.mul t P Q) = L'.mul t (pushPt (e j) (he j) P) (pushPt (e j) (he j) Q)),
        (letI := L'.pointCommGroup hc' f'
         (∀ j k : Fin (2 * 2), (∏ l, (⟨e l, he l⟩ : SchemeHomOver f' f') ^ (c j k l)) =
            ⟨e k ≫ e j, by rw [Category.assoc, he, he]⟩) ∧
         (∏ l, (⟨e l, he l⟩ : SchemeHomOver f' f') ^ (u l)) = ⟨𝟙 A', Category.id_comp _⟩) →
        ∃! i' : LatticeAction Λ f' L', ∀ j, i'.act (β j) = e j) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_LatticeAction_table_and_existsUnique_of_table.solution
