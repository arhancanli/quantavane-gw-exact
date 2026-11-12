module

public import GwExact.Rank
public import GwExact.Cert

@[expose] public section

/-!
# Upper bound: no colouring of `[1, 53]` with at most five colours avoids both progressions

`cert_ok` is the kernel check (`decide +kernel`, no `native_decide`) of the certificate
`GwExact.cert` against the GW CNF for `(n, R, l) = (53, 5, 4)`: 1,211 derived clauses, 28,114
hints, the last derived clause empty. With `gwProperty_of_check` (the checker's soundness and the
rank renaming) it gives the GW property at `53` for every `r ≤ 5`.
-/

namespace GwExact

theorem cert_ok : checkGw 53 5 4 cert = true := by decide +kernel

/-- For `r ≤ 5` colours: every colouring of `[1, n]`, `n ≥ 53`, has a rainbow 3-term AP or a
monochromatic 4-term AP. -/
theorem gwProperty_53_of_le {r : ℕ} (hr : r ≤ 5) : GWProperty r 4 53 := gwProperty_of_check hr cert_ok

end GwExact
