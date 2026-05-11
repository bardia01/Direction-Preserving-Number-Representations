import PaperProofs.Internal.OptimalAlphabets.Wyner

/-!
# Wyner's full spherical-cap covering theorem

Paper-facing aliases for the standalone formalization of Wyner's covering
asymptotic.
-/

noncomputable section

open Filter Topology Real Asymptotics

namespace PaperProofs

/-- Paper-facing notation for the true spherical-cap covering number. -/
abbrev Mc (n : Nat) (theta : Real) : Nat :=
  OptimalAlphabets.sphericalCapCoveringNumber n theta

/-- Paper-facing notation for Wyner's covering exponent. -/
abbrev Rc (theta : Real) : Real :=
  OptimalAlphabets.coveringExponent theta

/-- Wyner's full theorem, normalized-log formulation. -/
theorem theorem3_wyner_full_log_limit
    {theta : Real} (htheta0 : 0 < theta) (htheta_pi2 : theta < Real.pi / 2) :
    Tendsto
      (fun k : Nat =>
        Real.log ((Mc (k + 2) theta : Real)) / (((k + 2 : Nat) : Real)))
      atTop (𝓝 (Rc theta)) := by
  simpa [Mc, Rc] using
    OptimalAlphabets.wyner_sphericalCapCoveringNumber_log_limit
      htheta0 htheta_pi2

/-- Wyner's full theorem, little-o log-error formulation. -/
theorem theorem3_wyner_full_log_error_isLittleO
    {theta : Real} (htheta0 : 0 < theta) (htheta_pi2 : theta < Real.pi / 2) :
    (fun k : Nat =>
        Real.log ((Mc (k + 2) theta : Real)) -
          (((k + 2 : Nat) : Real) * Rc theta))
      =o[atTop] (fun k : Nat => (((k + 2 : Nat) : Real))) := by
  simpa [Mc, Rc] using
    OptimalAlphabets.wyner_sphericalCapCoveringNumber_log_error_isLittleO
      htheta0 htheta_pi2

end PaperProofs
