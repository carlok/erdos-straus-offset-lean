/-
  ESTheorem.lean — Machine-checked proof of the Erdős–Straus Unified Offset Theorem.

  Lean 4 + Mathlib.  Build:  lake build

  ==================================================================
  THEOREM (unified_offset_theorem).
  Let n, x, p, b, d1, d2, y, z ∈ ℤ satisfy
      (H1)  4 * x   = n + p           x  = (n+p)/4
      (H2)  b       = n * x           b  = n·(n+p)/4
      (H3)  d1 * d2 = b * b           d1·d2 = b²
      (H4)  p * y   = b + d1          y  = (b+d1)/p   (equivalently d1 ≡ -b mod p)
      (H5)  p * z   = b + d2          z  = (b+d2)/p
      (H6)  p ≠ 0
  Then  4 * x * y * z = n * (x*y + x*z + y*z).
  For positive n, x, y, z this integer identity is equivalent to
                                    4/n = 1/x + 1/y + 1/z.
  ==================================================================

  PROOF (machine-checked below).  Scale the goal by p².  Substituting
  b = n·x (H2) via `subst`, then p·y = b+d1 (H4) and p·z = b+d2 (H5) via
  rewrite, turns both sides into polynomials in (n, p, x, d1, d2); the residual
  from those substitutions is exactly p·(d1·d2 − b²), so `linear_combination`
  with the witness p·H3 closes the goal.  The p² factor is then cancelled using
  H6 (p ≠ 0).  Every algebraic step is discharged by `ring`.
-/

import Mathlib

namespace ESTheorem

/-- Helper: p ≠ 0 (p : ℤ) implies p * p ≠ 0. -/
lemma sq_nezero_int (q : ℤ) (hq : q ≠ 0) : q * q ≠ 0 := by
  intro h
  exact hq ((Int.mul_eq_zero.mp h).elim id id)

/-- The polynomial form of the Erdős–Straus identity.  For positive n, x, y, z
this is equivalent to 4/n = 1/x + 1/y + 1/z:
    4 * x * y * z = n * (x*y + x*z + y*z). -/
theorem es_polynomial (n x y z : ℤ)
    (h : 4 * x * y * z = n * (x * y + x * z + y * z)) :
    4 * x * y * z = n * (x * y + x * z + y * z) := h

/-! ## The engine lemma (the master tool)

The classical "divisor split" for the Erdős–Straus equation.  Fix integers
`n, x`; set `a = 4x - n` and `b = n x`.  The equation `1/y + 1/z = a/b` is
equivalent, on multiplying through by `a b y z`, to the factorisation
`(a y - b)(a z - b) = b^2`.  Hence any factorisation `d1 * d2 = b^2` with
`a | (b + d1)` and `a | (b + d2)` yields a valid solution `y = (b+d1)/a`,
`z = (b+d2)/a`.  The lemma below is exactly this, stated with `a = 4x - n` and
`b = n x` given explicitly (the weaker product form `a * b = (4x-n) * n x` does
NOT suffice — spurious factorisations of the product admit counterexamples). -/

theorem engine_lemma (n x a b d1 d2 y z : ℤ)
    (h_a  : a = 4 * x - n)
    (h_b  : b = n * x)
    (h_d  : d1 * d2 = b * b)
    (h_y  : a * y = b + d1)
    (h_z  : a * z = b + d2)
    (ha   : a ≠ 0)
    : 4 * x * y * z = n * (x * y + x * z + y * z) := by
  -- Substitute a := 4x-n, b := nx everywhere (goal + hypotheses).
  subst a b
  -- Scale goal by (4x-n)^2; substitute (4x-n)*y, (4x-n)*z via h_y, h_z (each
  -- step closed by `ring`), then close the residual with `linear_combination`
  -- using the witness d1*d2 − (n*x)^2.  Mirrors the unified-theorem proof.
  suffices H : (4*x-n) * (4*x-n) * (4 * x * y * z)
             = (4*x-n) * (4*x-n) * (n * (x * y + x * z + y * z)) by
    have ha' : (4 * x - n) * (4 * x - n) ≠ 0 := sq_nezero_int _ ha
    exact mul_left_cancel₀ ha' H
  have L : (4*x-n) * (4*x-n) * (4 * x * y * z) = 4 * x * (n*x + d1) * (n*x + d2) := by
    rw [← h_y, ← h_z]; ring
  have R : (4*x-n) * (4*x-n) * (n * (x * y + x * z + y * z))
         = n * ((4*x-n) * x * (n*x + d1) + (4*x-n) * x * (n*x + d2) + (n*x + d1) * (n*x + d2)) := by
    rw [← h_y, ← h_z]; ring
  rw [L, R]
  linear_combination (4 * x - n) * h_d

/-! ## Mordell's region `n ≡ 3 (mod 4)`

The first of Mordell's classical modular identities.  For `n` of the form
`4·k − 1` (equivalently `n ≡ 3 mod 4`), choosing `x = k` makes `a = 4x − n = 1`,
and the symmetric split `d1 = d2 = b` gives `y = z = 2b = n(n+1)/2`.  Parameterising
by `k` (so `n = 4k − 1`) sidesteps integer-division reasoning. -/

theorem mordell_3mod4 (k : ℤ)
    : ∃ x y z : ℤ, 4 * x * y * z = (4 * k - 1) * (x * y + x * z + y * z) := by
  -- n = 4k - 1, x = k, so a = 4k - (4k-1) = 1; y = z = 2*n*x.  Pure polynomial identity.
  exact ⟨k, 2 * (4 * k - 1) * k, 2 * (4 * k - 1) * k, by ring⟩

/-! ## Family I — `n ≡ 9 (mod 12)`  (i.e. `n ≡ 1 mod 4` ∧ `n ≡ 0 mod 3`)

For `n` of the form `12k + 9`, choosing `x = (n+3)/4 = 3k + 3` makes `4x − n = 3`,
which (since `3 | n`) reduces to `a = 1, b = n(n+3)/12`.  The split `d1 = 1`,
`d2 = b²` gives `y = b + 1, z = b(b + 1)`.  Parameterising by `k` keeps the
verification a pure `ring` check. -/

theorem family_I (k : ℤ)
    : ∃ x y z : ℤ, 4 * x * y * z = (12 * k + 9) * (x * y + x * z + y * z) := by
  -- n = 12k+9, x = 3k+3, b = n*x/3 = (12k+9)(3k+3)/3 = (12k+9)(k+1).
  -- y = b+1, z = b*(b+1).
  set n := (12 * k + 9 : ℤ)
  set x := (3 * k + 3 : ℤ)
  set b := (n * (k + 1) : ℤ)  -- = n*x/3
  exact ⟨x, b + 1, b * (b + 1), by ring⟩

/-- **Unified Offset Theorem** — the polynomial (integer) form, machine-checked.
This is the core algebraic content of the writeup's Theorem: under the six
hypotheses above, the Erdős–Straus polynomial identity holds. -/
theorem unified_offset_theorem (n x p b d1 d2 y z : ℤ)
    (h_x : 4 * x = n + p)
    (h_b : b = n * x)
    (h_d : d1 * d2 = b * b)
    (h_y : p * y = b + d1)
    (h_z : p * z = b + d2)
    (hp : p ≠ 0)
    : 4 * x * y * z = n * (x * y + x * z + y * z) := by
  -- It suffices to prove the goal scaled by p²; then cancel the nonzero p².
  suffices H : p * p * (4 * x * y * z) = p * p * (n * (x * y + x * z + y * z)) by
    exact mul_left_cancel₀ (sq_nezero_int p hp) H
  -- Eliminate b by definitional substitution (H2): b := n * x everywhere.
  subst b
  -- Left and right sides, rewritten via H4, H5; each step checked by `ring`.
  have L : p * p * (4 * x * y * z) = 4 * x * (n * x + d1) * (n * x + d2) := by
    rw [← h_y, ← h_z]; ring
  have R : p * p * (n * (x * y + x * z + y * z))
         = n * (x * p * (n * x + d1) + x * p * (n * x + d2) + (n * x + d1) * (n * x + d2)) := by
    rw [← h_y, ← h_z]; ring
  -- Substitute H1 (4x = n+p); the residual is exactly p·(d1·d2 − b²) = p·H3.
  rw [L, R, h_x]
  linear_combination p * h_d

/-! ## Positive natural-number formulation

The declarations below are the public, constructive interface used by the paper.
They retain the integer polynomial theorem above as an internal algebraic core,
but state the Erdős--Straus equation over positive natural numbers and rationals.
-/

/-- `IsES n x y z` means that `x,y,z` are positive natural-number denominators
giving an Erdős--Straus representation of the positive natural number `n`. -/
def IsES (n x y z : ℕ) : Prop :=
  0 < n ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧
    (4 : ℚ) / n = 1 / x + 1 / y + 1 / z

/-- A positive natural-number solution of the cross-multiplied polynomial
identity gives the corresponding rational unit-fraction identity. -/
theorem isES_of_polynomial (n x y z : ℕ)
    (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hpoly : 4 * x * y * z = n * (x * y + x * z + y * z)) :
    IsES n x y z := by
  refine ⟨hn, hx, hy, hz, ?_⟩
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hxq : (x : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hx)
  have hyq : (y : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hy)
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hz)
  have hpolyq :
      (4 : ℚ) * x * y * z = n * (x * y + x * z + y * z) := by
    exact_mod_cast hpoly
  field_simp [hnq, hxq, hyq, hzq]
  ring_nf at hpolyq ⊢
  exact hpolyq

/-- Positive certificate theorem.  The five equational hypotheses are a
division-free certificate for an Erdős--Straus representation. -/
theorem isES_of_offset_certificate (n x p b d1 d2 y z : ℕ)
    (hn : 0 < n) (hx : 0 < x) (hp : 0 < p)
    (hy : 0 < y) (hz : 0 < z)
    (h_x : 4 * x = n + p)
    (h_b : b = n * x)
    (h_d : d1 * d2 = b * b)
    (h_y : p * y = b + d1)
    (h_z : p * z = b + d2) :
    IsES n x y z := by
  apply isES_of_polynomial n x y z hn hx hy hz
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have hi := unified_offset_theorem
    (n : ℤ) (x : ℤ) (p : ℤ) (b : ℤ)
    (d1 : ℤ) (d2 : ℤ) (y : ℤ) (z : ℤ)
    (by exact_mod_cast h_x)
    (by exact_mod_cast h_b)
    (by exact_mod_cast h_d)
    (by exact_mod_cast h_y)
    (by exact_mod_cast h_z)
    hpz
  exact_mod_cast hi

/-- If the first factor is congruent to `-b` modulo a prime `p`, then so is
the complementary factor.  The proof performs cancellation in `ZMod p`. -/
theorem second_divisibility (p b d1 d2 : ℕ)
    (hp : Nat.Prime p)
    (hpb : ¬ p ∣ b)
    (hfactor : d1 * d2 = b * b)
    (hfirst : p ∣ b + d1) :
    p ∣ b + d2 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hb0 : (b : ZMod p) ≠ 0 := by
    intro h
    exact hpb ((ZMod.natCast_eq_zero_iff b p).mp h)
  have hsum1 : ((b + d1 : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff (b + d1) p).mpr hfirst
  have hd1 : (d1 : ZMod p) = -(b : ZMod p) := by
    push_cast at hsum1
    linear_combination hsum1
  have hd10 : (d1 : ZMod p) ≠ 0 := by
    rw [hd1]
    exact neg_ne_zero.mpr hb0
  have hfactor' : (d1 : ZMod p) * d2 = b * b := by
    simpa using congrArg (fun m : ℕ => (m : ZMod p)) hfactor
  have hd2 : (d2 : ZMod p) = -(b : ZMod p) := by
    apply mul_left_cancel₀ hd10
    calc
      (d1 : ZMod p) * d2 = b * b := hfactor'
      _ = (-b) * (-b) := by ring
      _ = (d1 : ZMod p) * (-b) := by rw [hd1]
  apply (ZMod.natCast_eq_zero_iff (b + d2) p).mp
  push_cast
  rw [hd2]
  exact add_neg_cancel _

/-- Fully constructive positive offset theorem.

For the displayed inputs, Lean constructs the denominators using natural-number
division, proves each division exact, proves positivity, and concludes the
rational Erdős--Straus identity.  The hypothesis `p ∣ b + d1` is the natural
number form of `d1 ≡ -b (mod p)`. -/
theorem constructive_offset (n p d1 : ℕ)
    (hn : 2 ≤ n)
    (hp : Nat.Prime p)
    (hp4 : p % 4 = 3)
    (hn4 : n % 4 = 1)
    (hpn : ¬ p ∣ n)
    (hd1 : 0 < d1)
    (hd1b : d1 ∣ n * ((n + p) / 4))
    (hfirst : p ∣ n * ((n + p) / 4) + d1) :
    let x := (n + p) / 4
    let b := n * x
    let d2 := b * b / d1
    let y := (b + d1) / p
    let z := (b + d2) / p
    IsES n x y z := by
  dsimp only
  let x := (n + p) / 4
  let b := n * x
  let d2 := b * b / d1
  let y := (b + d1) / p
  let z := (b + d2) / p
  have hp0 : 0 < p := hp.pos
  have hn0 : 0 < n := by omega
  have hfour : 4 ∣ n + p := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  have hxrel : 4 * x = n + p := by
    dsimp [x]
    exact Nat.mul_div_cancel' hfour
  have hx0 : 0 < x := by omega
  have hb0 : 0 < b := by
    dsimp [b]
    exact Nat.mul_pos hn0 hx0
  have hpx : ¬ p ∣ x := by
    intro h
    have hp4x : p ∣ 4 * x := dvd_mul_of_dvd_right h 4
    rw [hxrel] at hp4x
    exact hpn ((Nat.dvd_add_iff_left (dvd_refl p)).mpr hp4x)
  have hpb : ¬ p ∣ b := by
    intro h
    rcases hp.dvd_mul.mp (by simpa [b] using h) with h | h
    · exact hpn h
    · exact hpx h
  have hdprod : d1 ∣ b * b := by
    rcases hd1b with ⟨c, hc⟩
    refine ⟨c * b, ?_⟩
    dsimp [b, x] at hc ⊢
    rw [hc]
    ring
  have hfactor : d1 * d2 = b * b := by
    dsimp [d2]
    exact Nat.mul_div_cancel' hdprod
  have hsecond : p ∣ b + d2 :=
    second_divisibility p b d1 d2 hp hpb hfactor
      (by simpa [b, x] using hfirst)
  have hyrel : p * y = b + d1 := by
    dsimp [y]
    exact Nat.mul_div_cancel' (by simpa [b, x] using hfirst)
  have hzrel : p * z = b + d2 := by
    dsimp [z]
    exact Nat.mul_div_cancel' hsecond
  have hd20 : 0 < d2 := by
    by_contra h
    have hd2z : d2 = 0 := Nat.eq_zero_of_not_pos h
    rw [hd2z, mul_zero] at hfactor
    have : 0 < b * b := Nat.mul_pos hb0 hb0
    omega
  have hy0 : 0 < y := by
    apply Nat.pos_of_ne_zero
    intro hyz
    rw [hyz, mul_zero] at hyrel
    omega
  have hz0 : 0 < z := by
    apply Nat.pos_of_ne_zero
    intro hzz
    rw [hzz, mul_zero] at hzrel
    omega
  exact isES_of_offset_certificate n x p b d1 d2 y z
    hn0 hx0 hp0 hy0 hz0 hxrel rfl hfactor hyrel hzrel

/-- Direct regression example for the positive certificate:
`4/5 = 1/2 + 1/4 + 1/20`. -/
example : IsES 5 2 4 20 := by
  exact isES_of_offset_certificate 5 2 3 10 2 50 4 20
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ## Packaged offset admissibility -/

/-- The offset denominator \(X_p(n)=(n+p)/4\). -/
@[reducible] def offsetX (p n : ℕ) : ℕ := (n + p) / 4

/-- The associated product \(B_p(n)=nX_p(n)\). -/
@[reducible] def offsetB (p n : ℕ) : ℕ := n * offsetX p n

/-- `OffsetAdmissible p d n` packages exactly the hypotheses of
`constructive_offset` for the fixed divisor `d`. -/
def OffsetAdmissible (p d n : ℕ) : Prop :=
  2 ≤ n ∧
  Nat.Prime p ∧
  p % 4 = 3 ∧
  n % 4 = 1 ∧
  ¬ p ∣ n ∧
  0 < d ∧
  d ∣ offsetB p n ∧
  p ∣ offsetB p n + d

namespace OffsetAdmissible

/-- An admissible offset constructs a positive Erdős--Straus representation.
This is a packaged invocation of `constructive_offset`. -/
theorem isES {p d n : ℕ} (h : OffsetAdmissible p d n) :
    let x := offsetX p n
    let b := offsetB p n
    let d2 := b * b / d
    let y := (b + d) / p
    let z := (b + d2) / p
    IsES n x y z := by
  rcases h with ⟨hn, hp, hp4, hn4, hpn, hd, hdb, hfirst⟩
  simpa [offsetX, offsetB] using
    constructive_offset n p d hn hp hp4 hn4 hpn hd hdb hfirst

end OffsetAdmissible

/-! ## Transport through a fixed-divisor period -/

/-- The offset denominator changes linearly under the period `4 * p * d`. -/
theorem offsetX_add_period (p d n k : ℕ)
    (hp4 : p % 4 = 3) (hn4 : n % 4 = 1) :
    offsetX p (n + 4 * p * d * k) = offsetX p n + p * d * k := by
  have hfour : 4 ∣ n + p := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  have hbase : 4 * offsetX p n = n + p := by
    exact Nat.mul_div_cancel' hfour
  change (n + 4 * p * d * k + p) / 4 = (n + p) / 4 + p * d * k
  have hperiod : 4 * p * d * k = 4 * (p * d * k) := by ring
  rw [hperiod]
  omega

/-- Exact transport identity for the associated product `B_p`. -/
theorem offsetB_add_period (p d n k : ℕ)
    (hp4 : p % 4 = 3) (hn4 : n % 4 = 1) :
    offsetB p (n + 4 * p * d * k) =
      offsetB p n +
        p * d * k * (n + 4 * offsetX p n + 4 * p * d * k) := by
  unfold offsetB
  rw [offsetX_add_period p d n k hp4 hn4]
  ring

namespace OffsetAdmissible

/-- Admissibility is preserved on adding any multiple of the period `4*p*d`. -/
theorem add_period {p d n : ℕ} (h : OffsetAdmissible p d n) (k : ℕ) :
    OffsetAdmissible p d (n + 4 * p * d * k) := by
  rcases h with ⟨hn, hp, hp4, hn4, hpn, hd, hdb, hfirst⟩
  have hperiod4 : 4 ∣ 4 * p * d * k := by
    refine ⟨p * d * k, ?_⟩
    ring
  have hperiodp : p ∣ 4 * p * d * k := by
    refine ⟨4 * d * k, ?_⟩
    ring
  have hB := offsetB_add_period p d n k hp4 hn4
  let q := n + 4 * offsetX p n + 4 * p * d * k
  have hdeltaD : d ∣ p * d * k * q := by
    refine ⟨p * k * q, ?_⟩
    ring
  have hdeltaP : p ∣ p * d * k * q := by
    refine ⟨d * k * q, ?_⟩
    ring
  refine ⟨by omega, hp, hp4, ?_, ?_, hd, ?_, ?_⟩
  · simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hperiod4, hn4]
  · intro hnew
    exact hpn ((Nat.dvd_add_iff_left hperiodp).mpr hnew)
  · rw [hB]
    exact Nat.dvd_add hdb (by simpa [q] using hdeltaD)
  · rw [hB]
    convert Nat.dvd_add hfirst (by simpa [q] using hdeltaP) using 1
    ring

end OffsetAdmissible

/-! ## Verified fixed-divisor progressions -/

/-- Every point of a fixed-divisor admissible progression has a constructed
positive Erdős--Straus representation. -/
theorem fixed_d_progression {p d n : ℕ}
    (h : OffsetAdmissible p d n) (k : ℕ) :
    let n' := n + 4 * p * d * k
    let x := offsetX p n'
    let b := offsetB p n'
    let d2 := b * b / d
    let y := (b + d) / p
    let z := (b + d2) / p
    IsES n' x y z :=
  (h.add_period k).isES

/-- The parameters `n + 4*p*d*k` form a strictly increasing sequence. -/
theorem fixed_d_progression_strictMono {p d n : ℕ}
    (h : OffsetAdmissible p d n) :
    StrictMono (fun k : ℕ => n + 4 * p * d * k) := by
  rcases h with ⟨_, hp, _, _, _, hd, _, _⟩
  have hp0 : 0 < p := hp.pos
  intro a b hab
  have hc : 0 < 4 * p * d := by positivity
  have hm : (4 * p * d) * a < (4 * p * d) * b :=
    (Nat.mul_lt_mul_left hc).mpr hab
  exact Nat.add_lt_add_left hm n

/-! ## General transport and period characterization

The lemmas `offsetX_add_period` and `offsetB_add_period` above establish transport
for the *specific* period `T = 4 * p * d * k`.  The results below work with an
arbitrary `T` divisible by four.  They are algebraic tools for a subsequent
characterization of transport periods; no novelty or minimality claim is made
by these identities alone. -/

/-- General transport identity for `offsetX`: for any `T` with `4 ∣ T`,
`offsetX(p, n+T) = offsetX(p,n) + T/4`.  (Identity A.) -/
theorem offsetX_add_general (p n T : ℕ) (hp4 : p % 4 = 3) (hn4 : n % 4 = 1)
    (hT : 4 ∣ T) :
    offsetX p (n + T) = offsetX p n + T / 4 := by
  have hfour_n : 4 ∣ n + p := by apply Nat.dvd_of_mod_eq_zero; omega
  have hfour_nT : 4 ∣ n + T + p := by omega
  have hbase : 4 * ((n + p) / 4) = n + p := Nat.mul_div_cancel' hfour_n
  have hnew : 4 * ((n + T + p) / 4) = n + T + p := Nat.mul_div_cancel' hfour_nT
  have hT4 : 4 * (T / 4) = T := Nat.mul_div_cancel' hT
  simp only [offsetX]
  omega

/-- General transport identity for `offsetB`: for any `T` with `4 ∣ T`, writing
`u = T/4`, `offsetB(p, n+T) = offsetB(p,n) + u*(n + 4*offsetX(p,n) + 4*u)`.
(Identity B.) -/
theorem offsetB_add_general (p n T : ℕ) (hp4 : p % 4 = 3) (hn4 : n % 4 = 1)
    (hT : 4 ∣ T) :
    offsetB p (n + T) =
      offsetB p n + (T / 4) * (n + 4 * offsetX p n + 4 * (T / 4)) := by
  -- Pull out u = T/4 with the exact equation 4*u = T, so `ring` sees no division.
  obtain ⟨u, hu⟩ : ∃ u : ℕ, 4 * u = T := ⟨T / 4, Nat.mul_div_cancel' hT⟩
  have hx := offsetX_add_general p n T hp4 hn4 hT
  simp only [offsetB, hx, show T / 4 = u from by omega]
  subst hu
  ring

/-- Polynomial-divisibility lemma: `d ∣ a₁*k + a₂*k²` for all `k ∈ ℕ` iff
`d ∣ (a₁+a₂)` and `d ∣ 2*a₂`.  (⟸ uses `k(k−1)` even; ⟹ evaluates at k=1,2.)
Standalone; used by the period-characterization theorem. -/
theorem poly_dvd_all (d a1 a2 : ℕ) :
    (∀ k : ℕ, d ∣ a1 * k + a2 * k * k) ↔ d ∣ (a1 + a2) ∧ d ∣ 2 * a2 := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨hs, h2⟩ k => ?_⟩
  · -- Evaluate at `k = 1`.
    have h1 : d ∣ a1 * 1 + a2 * 1 * 1 := h 1
    convert h1 using 1; ring
  · -- Subtract twice the value at `k = 1` from the value at `k = 2`.
    have h1 : d ∣ a1 + a2 := by
      convert h 1 using 1
      ring
    have h2k : d ∣ a1 * 2 + a2 * 2 * 2 := h 2
    have hdouble : d ∣ 2 * (a1 + a2) :=
      dvd_mul_of_dvd_right h1 2
    have hsub := Nat.dvd_sub h2k hdouble
    convert hsub using 1
    omega
  · -- For `k+1`, split off `(k+1)(a1+a2)`; the remaining product
    -- contains the even number `k(k+1)`.
    rcases k with _ | k
    · simp
    · have heq :
          a1 * (k + 1) + a2 * (k + 1) * (k + 1) =
            (k + 1) * (a1 + a2) + a2 * ((k + 1) * k) := by
        ring
      rw [heq]
      apply Nat.dvd_add
      · exact dvd_mul_of_dvd_right hs (k + 1)
      · obtain ⟨v, hv⟩ := Nat.two_dvd_mul_add_one k
        have hv' : (k + 1) * k = 2 * v := by
          simpa [mul_comm] using hv
        rw [hv']
        simpa [mul_assoc, mul_comm, mul_left_comm] using
          dvd_mul_of_dvd_right h2 v

/-- Expansion of `offsetB` along an arbitrary step divisible by four. -/
theorem offsetB_add_four_mul (p n u k : ℕ)
    (hp4 : p % 4 = 3) (hn4 : n % 4 = 1) :
    offsetB p (n + 4 * u * k) =
      offsetB p n +
        (u * (n + 4 * offsetX p n)) * k + (4 * u * u) * k * k := by
  have hfour : 4 ∣ 4 * u * k := by
    refine ⟨u * k, ?_⟩
    ring
  have hquot : (4 * u * k) / 4 = u * k := by
    simp [mul_assoc]
  rw [offsetB_add_general p n (4 * u * k) hp4 hn4 hfour, hquot]
  ring

/-- If no member of the progression `n + T*k` is divisible by a prime `p`,
then the step `T` is divisible by `p`. -/
private theorem prime_dvd_step_of_forall_not_dvd (p n T : ℕ)
    (hp : Nat.Prime p) (hnever : ∀ k : ℕ, ¬ p ∣ n + T * k) :
    p ∣ T := by
  by_contra hT
  letI : Fact p.Prime := ⟨hp⟩
  have hT0 : (T : ZMod p) ≠ 0 := by
    intro hz
    exact hT ((ZMod.natCast_eq_zero_iff T p).mp hz)
  let a : ZMod p := -(n : ZMod p) / (T : ZMod p)
  let k : ℕ := a.val
  have hk : (k : ZMod p) = a := ZMod.natCast_zmod_val a
  have hzero : ((n + T * k : ℕ) : ZMod p) = 0 := by
    push_cast
    rw [hk]
    dsimp [a]
    field_simp
    simp
  exact hnever k ((ZMod.natCast_eq_zero_iff (n + T * k) p).mp hzero)

namespace OffsetAdmissible

/-- Characterization of all positive transport periods for one admissible seed.
The first two conditions are forced by the mod-four and nondivisibility
hypotheses.  The last two are exactly the conditions for the quadratic change
in `offsetB` to remain divisible by `d`. -/
theorem all_add_mul_iff {p d n T : ℕ} (h : OffsetAdmissible p d n)
    (hT0 : 0 < T) :
    (∀ k : ℕ, OffsetAdmissible p d (n + T * k)) ↔
      4 ∣ T ∧
      p ∣ T ∧
      d ∣ 8 * (T / 4) * (T / 4) ∧
      d ∣ (T / 4) * (n + 4 * offsetX p n + 4 * (T / 4)) := by
  rcases h with ⟨hn, hp, hp4, hn4, hpn, hd, hdb, hfirst⟩
  constructor
  · intro hall
    have h4 : 4 ∣ T := by
      apply Nat.dvd_of_mod_eq_zero
      have hnT4 := (hall 1).2.2.2
      omega
    have hpT : p ∣ T := by
      apply prime_dvd_step_of_forall_not_dvd p n T hp
      intro k
      exact (hall k).2.2.2.2.1
    rcases h4 with ⟨u, rfl⟩
    have hpoly :
        ∀ k : ℕ,
          d ∣ (u * (n + 4 * offsetX p n)) * k + (4 * u * u) * k * k := by
      intro k
      have hnew : d ∣ offsetB p (n + 4 * u * k) :=
        (hall k).2.2.2.2.2.2.1
      rw [offsetB_add_four_mul p n u k hp4 hn4] at hnew
      apply (Nat.dvd_add_iff_right hdb).mpr
      convert hnew using 1
      ring
    have hcoeff :=
      (poly_dvd_all d (u * (n + 4 * offsetX p n)) (4 * u * u)).mp hpoly
    have hquot : (4 * u) / 4 = u := by omega
    refine ⟨by simp, by simpa using hpT, ?_, ?_⟩
    · simp only [hquot]
      convert hcoeff.2 using 1
      ring
    · simpa [hquot, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm] using hcoeff.1
  · rintro ⟨h4, hpT, hdquad, hdlin⟩
    rcases h4 with ⟨u, rfl⟩
    have hp4not : ¬ p ∣ 4 := by
      intro hp4dvd
      have hp_le : p ≤ 4 := Nat.le_of_dvd (by norm_num) hp4dvd
      have hp_ge : 2 ≤ p := hp.two_le
      have : p = 3 := by omega
      subst p
      norm_num at hp4dvd
    have hpu : p ∣ u := by
      rcases hp.dvd_mul.mp (by simpa [mul_assoc] using hpT) with hp4dvd | hpu
      · exact (hp4not hp4dvd).elim
      · exact hpu
    have hquot : (4 * u) / 4 = u := by omega
    have hcoeff :
        d ∣ u * (n + 4 * offsetX p n) + 4 * u * u ∧
          d ∣ 2 * (4 * u * u) := by
      constructor
      · simpa [hquot, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm] using hdlin
      · simpa [hquot, pow_two, mul_assoc, mul_comm, mul_left_comm] using hdquad
    have hpoly :
        ∀ k : ℕ,
          d ∣ (u * (n + 4 * offsetX p n)) * k + (4 * u * u) * k * k :=
      (poly_dvd_all d (u * (n + 4 * offsetX p n)) (4 * u * u)).mpr hcoeff
    intro k
    have hshift4 : 4 ∣ 4 * u * k := by
      refine ⟨u * k, ?_⟩
      ring
    have hshiftp : p ∣ 4 * u * k := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hpu 4) k
    have hdeltaP :
        p ∣ (u * (n + 4 * offsetX p n)) * k + (4 * u * u) * k * k := by
      apply Nat.dvd_add
      · simpa [mul_assoc, mul_comm, mul_left_comm] using
          dvd_mul_of_dvd_right
            (dvd_mul_of_dvd_right hpu (n + 4 * offsetX p n)) k
      · simpa [mul_assoc, mul_comm, mul_left_comm] using
          dvd_mul_of_dvd_right
            (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hpu 4) u) (k * k)
    refine ⟨by omega, hp, hp4, ?_, ?_, hd, ?_, ?_⟩
    · simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hshift4, hn4]
    · intro hnew
      exact hpn ((Nat.dvd_add_iff_left hshiftp).mpr hnew)
    · rw [offsetB_add_four_mul p n u k hp4 hn4]
      convert Nat.dvd_add hdb (hpoly k) using 1
      ring
    · rw [offsetB_add_four_mul p n u k hp4 hn4]
      convert Nat.dvd_add hfirst hdeltaP using 1
      ring

end OffsetAdmissible

/-! ## Fully verified infinite families
-/

/-- Family I: `n = 12k+9`. -/
theorem family_I_positive (k : ℕ) :
    let n := 12 * k + 9
    let x := 3 * k + 3
    let b := n * (k + 1)
    IsES n x (b + 1) (b * (b + 1)) := by
  dsimp only
  apply isES_of_polynomial
  · omega
  · omega
  · positivity
  · positivity
  · ring

private theorem admissible_d2_5 : OffsetAdmissible 3 2 5 := by
  norm_num [OffsetAdmissible, offsetB, offsetX]

private theorem admissible_d2_13 : OffsetAdmissible 3 2 13 := by
  norm_num [OffsetAdmissible, offsetB, offsetX]

private theorem admissible_d5_5 : OffsetAdmissible 3 5 5 := by
  norm_num [OffsetAdmissible, offsetB, offsetX]

private theorem admissible_d5_17 : OffsetAdmissible 3 5 17 := by
  norm_num [OffsetAdmissible, offsetB, offsetX]

private theorem admissible_d5_25 : OffsetAdmissible 3 5 25 := by
  norm_num [OffsetAdmissible, offsetB, offsetX]

private theorem admissible_d5_37 : OffsetAdmissible 3 5 37 := by
  norm_num [OffsetAdmissible, offsetB, offsetX]

/-- Regression: the tempting half-step `12` does not preserve the
`p = 3, d = 2, n = 5` admissible seed. -/
example : ¬ ∀ k : ℕ, OffsetAdmissible 3 2 (5 + 12 * k) := by
  rw [admissible_d2_5.all_add_mul_iff (by norm_num : 0 < 12)]
  norm_num [offsetX]

/-- The `p=3, d1=2` progression `n = 24k+5`. -/
theorem family_d2_24k5 (k : ℕ) :
    let n := 24 * k + 5
    let x := (n + 3) / 4
    let b := n * x
    IsES n x ((b + 2) / 3) ((b + b * b / 2) / 3) := by
  have hn : 5 + 4 * 3 * 2 * k = 24 * k + 5 := by ring
  simpa only [offsetX, offsetB, hn] using
    fixed_d_progression admissible_d2_5 k

/-- The `p=3, d1=2` progression `n = 24k+13`. -/
theorem family_d2_24k13 (k : ℕ) :
    let n := 24 * k + 13
    let x := (n + 3) / 4
    let b := n * x
    IsES n x ((b + 2) / 3) ((b + b * b / 2) / 3) := by
  have hn : 13 + 4 * 3 * 2 * k = 24 * k + 13 := by ring
  simpa only [offsetX, offsetB, hn] using
    fixed_d_progression admissible_d2_13 k

/-- The `p=3, d1=5` progression `n = 60k+5`. -/
theorem family_d5_60k5 (k : ℕ) :
    let n := 60 * k + 5
    let x := (n + 3) / 4
    let b := n * x
    IsES n x ((b + 5) / 3) ((b + b * b / 5) / 3) := by
  have hn : 5 + 4 * 3 * 5 * k = 60 * k + 5 := by ring
  simpa only [offsetX, offsetB, hn] using
    fixed_d_progression admissible_d5_5 k

/-- The `p=3, d1=5` progression `n = 60k+17`. -/
theorem family_d5_60k17 (k : ℕ) :
    let n := 60 * k + 17
    let x := (n + 3) / 4
    let b := n * x
    IsES n x ((b + 5) / 3) ((b + b * b / 5) / 3) := by
  have hn : 17 + 4 * 3 * 5 * k = 60 * k + 17 := by ring
  simpa only [offsetX, offsetB, hn] using
    fixed_d_progression admissible_d5_17 k

/-- The `p=3, d1=5` progression `n = 60k+25`. -/
theorem family_d5_60k25 (k : ℕ) :
    let n := 60 * k + 25
    let x := (n + 3) / 4
    let b := n * x
    IsES n x ((b + 5) / 3) ((b + b * b / 5) / 3) := by
  have hn : 25 + 4 * 3 * 5 * k = 60 * k + 25 := by ring
  simpa only [offsetX, offsetB, hn] using
    fixed_d_progression admissible_d5_25 k

/-- The `p=3, d1=5` progression `n = 60k+37`. -/
theorem family_d5_60k37 (k : ℕ) :
    let n := 60 * k + 37
    let x := (n + 3) / 4
    let b := n * x
    IsES n x ((b + 5) / 3) ((b + b * b / 5) / 3) := by
  have hn : 37 + 4 * 3 * 5 * k = 60 * k + 37 := by ring
  simpa only [offsetX, offsetB, hn] using
    fixed_d_progression admissible_d5_37 k

/- Regression instances at `k=0` and `k=1` for every progression. -/

example : IsES 9 3 10 90 := by simpa using family_I_positive 0
example : IsES 21 6 43 1806 := by simpa using family_I_positive 1

example : IsES 5 2 4 20 := by simpa using family_d2_24k5 0
example : IsES 29 8 78 9048 := by simpa using family_d2_24k5 1
example : IsES 13 4 18 468 := by simpa using family_d2_24k13 0
example : IsES 37 10 124 22940 := by simpa using family_d2_24k13 1

example : IsES 5 2 5 10 := by simpa using family_d5_60k5 0
example : IsES 65 17 370 81770 := by simpa using family_d5_60k5 1
example : IsES 17 5 30 510 := by simpa using family_d5_60k17 0
example : IsES 77 20 515 158620 := by simpa using family_d5_60k17 1
example : IsES 25 7 60 2100 := by simpa using family_d5_60k25 0
example : IsES 85 22 625 233750 := by simpa using family_d5_60k25 1
example : IsES 37 10 125 9250 := by simpa using family_d5_60k37 0
example : IsES 97 25 810 392850 := by simpa using family_d5_60k37 1

end ESTheorem
