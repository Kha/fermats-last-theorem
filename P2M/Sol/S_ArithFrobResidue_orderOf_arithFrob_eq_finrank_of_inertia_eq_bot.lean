import Definitions.Def_ArithFrobResidue
import P2M.Util
namespace P2MW.S_ArithFrobResidue_orderOf_arithFrob_eq_finrank_of_inertia_eq_bot
open scoped Pointwise
attribute [local instance] Ideal.Quotient.field
theorem solution
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    {P : Ideal B} [P.IsMaximal] [(P.under A).IsMaximal]
    [Fintype (A ⧸ P.under A)] [Finite (B ⧸ P)]
    (hP : P.inertia G = ⊥)
    (σ : MulAction.stabilizer G P) (hσ : IsArithFrobAt A (σ : G) P) :
    orderOf (σ : G) = Module.finrank (A ⧸ P.under A) (B ⧸ P) :=
  ArithFrobResidue.orderOf_arithFrob_eq_finrank_of_inertia_eq_bot hP σ hσ
