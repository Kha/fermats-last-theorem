import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.NumberTheory.RamificationInertia.Galois
import P2M.Util
import P2M.Sol.S_ArithFrob_isArithFrobAt_unique

set_option autoImplicit false

open MulAction
open scoped Pointwise

theorem ArithFrob.isArithFrobAt_unique {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    {P : Ideal B} [P.IsMaximal] [(P.under A).IsMaximal]
    [Fintype (A ⧸ P.under A)] [Finite (B ⧸ P)]
    {σ₁ σ₂ : G} (h₁ : IsArithFrobAt A σ₁ P) (h₂ : IsArithFrobAt A σ₂ P)
    (hin : P.inertia G = ⊥) : σ₁ = σ₂:= by p2m_exact_reverting @_root_.P2MW.S_ArithFrob_isArithFrobAt_unique.solution
