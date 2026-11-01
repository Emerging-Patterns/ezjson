# The rounded digits are written as the integer part, every digit before the
# last `n` with its leading `0`s dropped (`0` when none is left), followed by
# `.` and the last `n` digits when `n` is at least 1, and by nothing when `n`
# is 0: no point, as Python writes `'%.0f' % 2.5` as `2`
import Base
import ../src/fixed.bend as F

# LAW: the rounded digits (last first) are written as the integer part, the
# digits before the last nn, and the fraction, the last nn
law write_parts:
  for +nn: Nat
  for +digits: String
  {F.write(nn, digits)
    == F.point(nn, F.trim(String.reverse(String.drop(digits, nn))),
      String.reverse(String.take(digits, nn))) : String}

# LAW: no places writes the integer part alone, with no point
law point_none:
  for +int: String
  for +frac: String
  {F.point(0n, int, frac) == int : String}

# LAW: one or more places write the integer part, a point and the fraction
law point_some:
  for +mm: Nat
  for +int: String
  for +frac: String
  {F.point(1n+mm, int, frac) == int ++ "." ++ frac : String}

# LAW: a leading 0 of the integer part is dropped
law trim_zero:
  for +tl: String
  {F.trim(SCon{'0', tl}) == F.trim(tl) : String}

# LAW: an integer part that starts with another digit is kept whole
law trim_lead:
  for +ch: Char
  for +tl: String
  for +h: {Char.is_eq(ch, '0') == False{} : Bool}
  {F.trim(SCon{ch, tl}) == SCon{ch, tl} : String}

# LAW: an integer part of only 0s, or none, is written 0
law trim_zeros:
  for +kk: Nat
  {F.trim(String.repeat("0", kk)) == "0" : String}
