import Mathlib.RingTheory.Frobenius
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import P2M.Util
import P2M.Sol.S_ArithFrobResidue_orderOf_arithFrob_eq_finrank_of_inertia_eq_bot
import Definitions.Def_ArithFrobResidue

open scoped Pointwise
attribute [local instance] Ideal.Quotient.field
theorem P2M.Dup.ArithFrobResidue.orderOf_arithFrob_eq_finrank_of_inertia_eq_bot
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    {P : Ideal B} [P.IsMaximal] [(P.under A).IsMaximal]
    [Fintype (A ⧸ P.under A)] [Finite (B ⧸ P)]
    (hP : P.inertia G = ⊥)
    (σ : MulAction.stabilizer G P) (hσ : IsArithFrobAt A (σ : G) P) :
    orderOf (σ : G) = Module.finrank (A ⧸ P.under A) (B ⧸ P) := by p2m_exact_reverting @_root_.P2MW.S_ArithFrobResidue_orderOf_arithFrob_eq_finrank_of_inertia_eq_bot.solution
#p2m_type_eq_warn P2M.Dup.ArithFrobResidue.orderOf_arithFrob_eq_finrank_of_inertia_eq_bot ArithFrobResidue.orderOf_arithFrob_eq_finrank_of_inertia_eq_bot
