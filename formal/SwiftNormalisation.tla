------------------------- MODULE SwiftNormalisation -------------------------
(* Finite model of Sources/SwiftNormalisation: Normalisation.scale,          *)
(* scaleFrom0To1 and scaleFrom0To100.                                         *)
(* Double is abstracted to EXACT rationals <<num, den>> (den > 0); inputs     *)
(* are small integers. IEEE-754 rounding, NaN and infinity are out of scope;  *)
(* the degenerate measure range (min == max) is excluded from every law (in   *)
(* Swift it yields NaN / inf, see README).                                    *)
EXTENDS Integers

CONSTANTS Lim,     \* integers range over -Lim..Lim
          Mutant   \* "none" or a seeded bug

VARIABLE u
Init == u = 0
Next == UNCHANGED u
Spec == Init /\ [][Next]_u

(* ---- exact rationals ---- *)
Q(n, d)  == IF d < 0 THEN <<-n, -d>> ELSE <<n, d>>
I(n)     == <<n, 1>>
Add(p, q) == Q(p[1] * q[2] + q[1] * p[2], p[2] * q[2])
Sub(p, q) == Q(p[1] * q[2] - q[1] * p[2], p[2] * q[2])
Mul(p, q) == Q(p[1] * q[1], p[2] * q[2])
Div(p, q) == Q(p[1] * q[2], p[2] * q[1])          \* q # 0
QEq(p, q) == p[1] * q[2] = q[1] * p[2]
QLt(p, q) == p[1] * q[2] < q[1] * p[2]
QLe(p, q) == QEq(p, q) \/ QLt(p, q)

(* ---- Normalisation.swift ---- *)
\* (maxScale - minScale) * ((number - minMeasure) / (maxMeasure - minMeasure)) + minScale
Scale(x, mM, MM, mS, MS) ==
  LET xx    == IF Mutant = "clamps_result" THEN (IF x < mM THEN mM ELSE IF x > MM THEN MM ELSE x) ELSE x
      denom == IF Mutant = "denominator_wrong" THEN MM ELSE MM - mM
  IN  IF Mutant = "off_by_min"
        THEN Mul(I(MS - mS), Div(I(xx - mM), I(denom)))
        ELSE Add(Mul(I(MS - mS), Div(I(xx - mM), I(denom))), I(mS))

From0To1(x, mn, mx)   == Scale(x, mn, mx, 0, 1)
From0To100(x, lo, hi) == Scale(x, lo, hi, 0, IF Mutant = "from0to100_uses_99" THEN 99 ELSE 100)

Ints   == -Lim..Lim
MRs    == {r \in Ints \X Ints : r[1] < r[2]}      \* non-degenerate measure ranges
SRs    == Ints \X Ints                              \* scale ranges, any order, may be degenerate
Xs     == Ints

TypeOK == u = 0 /\ MRs # {} /\ SRs # {}

EndpointsMapToEndpoints == u = 0 =>
  \A m \in MRs, s \in SRs :
    QEq(Scale(m[1], m[1], m[2], s[1], s[2]), I(s[1])) /\
    QEq(Scale(m[2], m[1], m[2], s[1], s[2]), I(s[2]))

\* number inside the measure range stays between the scale bounds (docs: "in range minScale...maxScale")
InRangeStaysInRange == u = 0 =>
  \A m \in MRs, s \in SRs, x \in Xs : (m[1] <= x /\ x <= m[2]) =>
    LET r == Scale(x, m[1], m[2], s[1], s[2])
    IN  IF s[1] <= s[2] THEN QLe(I(s[1]), r) /\ QLe(r, I(s[2]))
                        ELSE QLe(I(s[2]), r) /\ QLe(r, I(s[1]))

MonotoneWithScaleOrientation == u = 0 =>
  \A m \in MRs, s \in SRs, x, y \in Xs : x < y =>
    LET a == Scale(x, m[1], m[2], s[1], s[2])
        b == Scale(y, m[1], m[2], s[1], s[2])
    IN  /\ (s[1] < s[2] => QLt(a, b))
        /\ (s[1] > s[2] => QLt(b, a))
        /\ (s[1] = s[2] => QEq(a, b))

DegenerateScaleIsConstant == u = 0 =>
  \A m \in MRs, x \in Xs, c \in Ints : QEq(Scale(x, m[1], m[2], c, c), I(c))

\* linear: a unit step in the input moves the output by (maxScale-minScale)/(maxMeasure-minMeasure)
ConstantStep == u = 0 =>
  \A m \in MRs, s \in SRs, x \in Xs : x + 1 <= Lim =>
    QEq(Sub(Scale(x + 1, m[1], m[2], s[1], s[2]), Scale(x, m[1], m[2], s[1], s[2])),
        Div(I(s[2] - s[1]), I(m[2] - m[1])))

IdentityOnSameRange == u = 0 =>
  \A m \in MRs, x \in Xs : QEq(Scale(x, m[1], m[2], m[1], m[2]), I(x))

\* scaling to another range and back (swapping the roles) returns the input
InverseRoundTrip == u = 0 =>
  \A m \in MRs, s \in MRs, x \in Xs :
    LET r == Scale(x, m[1], m[2], s[1], s[2])
        \* second hop needs a rational input, so evaluate the formula directly
        back == Add(Mul(I(m[2] - m[1]), Div(Sub(r, I(s[1])), I(s[2] - s[1]))), I(m[1]))
    IN  QEq(back, I(x))

\* the function never clamps: outside the measure range it extrapolates
NoClamping == u = 0 =>
  \A m \in MRs, s \in MRs, x \in Xs :
    /\ x > m[2] => QLt(I(s[2]), Scale(x, m[1], m[2], s[1], s[2]))
    /\ x < m[1] => QLt(Scale(x, m[1], m[2], s[1], s[2]), I(s[1]))

From0To1IsScaleTo01 == u = 0 =>
  \A m \in MRs, x \in Xs : QEq(From0To1(x, m[1], m[2]), Scale(x, m[1], m[2], 0, 1))
From0To1EndpointsAndRange == u = 0 =>
  \A m \in MRs : QEq(From0To1(m[1], m[1], m[2]), I(0)) /\ QEq(From0To1(m[2], m[1], m[2]), I(1))
From0To100IsHundredTimesFrom0To1 == u = 0 =>
  \A m \in MRs, x \in Xs :
    QEq(From0To100(x, m[1], m[2]), Mul(I(100), From0To1(x, m[1], m[2])))
=============================================================================
