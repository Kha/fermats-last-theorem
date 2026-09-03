import Mathlib.Tactic.LinearCombination
import P2M.Util
import P2M.Sol.S_ModularCurve_psiFifteen_birational_identity

theorem ModularCurve.psiFifteen_birational_identity (u v : ℚ)
    (hpsi : (u + 27) * (u + 3) ^ 3 * v - u * (v ^ 2 + 10 * v + 5) ^ 3 = 0)
    (Nx Dx Ny Dy : ℚ)
    (hNx : Nx = 135 - 1701 * v - 972 * v ^ 2 - 108 * v ^ 3 + 250 * u - 146 * u * v
      - 12 * u * v ^ 2 - 8 * u * v ^ 3 + 15 * u ^ 2 - 13 * u ^ 2 * v)
    (hDx : Dx = 1458 * v + 621 * v ^ 2 + 54 * v ^ 3 - 250 * u - 7 * u * v - 24 * u * v ^ 2
      - u * v ^ 3 - 15 * u ^ 2 + 4 * u ^ 2 * v)
    (hNy : Ny = 64125 - 196047 * v - 86022 * v ^ 2 - 5778 * v ^ 3 + 10125 * u - 79605 * u * v
      - 10035 * u * v ^ 2 + 225 * u * v ^ 3 - 432 * u ^ 2 * v + 63 * u ^ 2 * v ^ 2
      + 27 * u ^ 2 * v ^ 3 + 90 * u ^ 3 * v)
    (hDy : Dy = 134136 * v + 43011 * v ^ 2 + 2889 * v ^ 3 - 23000 * u + 290 * u * v
      + 2930 * u * v ^ 2 + 225 * u * v ^ 3 - 1125 * u ^ 2 - 484 * u ^ 2 * v - 44 * u ^ 2 * v ^ 2
      - u ^ 2 * v ^ 3 + 5 * u ^ 3 * v) :
    Ny ^ 2 * Dx ^ 3 + Nx * Ny * Dx ^ 2 * Dy + Ny * Dx ^ 3 * Dy - Nx ^ 3 * Dy ^ 2
      - Nx ^ 2 * Dx * Dy ^ 2 + 10 * Nx * Dx ^ 2 * Dy ^ 2 + 10 * Dx ^ 3 * Dy ^ 2 = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_psiFifteen_birational_identity.solution
