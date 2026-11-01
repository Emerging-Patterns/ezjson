# For every text `s` and count `n`, `num.fixed(s, n)` is `None` when
# `num.ok(s)` is false, and `Some{F.text(s, n)}` when it is true, where
# `F.text` is `src/fixed.bend`'s writer that laws/FixedKeepsMinus.bend to
# laws/FixedWritesDigits.bend describe
#
# `num.fixed(s, n)` writes a number's text with exactly `n` digits after the
# point, rounding half to even on its decimal digits. The reference is
# Python's `format(Decimal(s).quantize(Decimal(10) ** -n, ROUND_HALF_EVEN),
# 'f')`, which is IEEE 754's roundTiesToEven applied to the exact decimal
# value of `s`; on every input where that decimal value is exactly a binary
# double, this is also Python's `'%.{n}f' % float(s)` (C's `printf("%.*f")`).
# Python's `'%.Nf'` rounds the double nearest to `s`, not `s`, so the two
# differ where the double falls on the other side of a rounding boundary:
# `2.675` to 2 places is `2.68` here and `2.67` in Python (the double is
# 2.67499999999999982236431605997495353221893310546875), `0.15` to 1 is `0.2`
# here and `0.1` there, `0.45` is `0.4` here and `0.5` there, `0.0005` to 3 is
# `0.000` here and `0.001` there, `9.995` to 2 is `10.00` here and `9.99`
# there. They also differ past the 17 significant digits a double holds
# (`1e23` to 0 places is a 1 and 23 zeros here, `99999999999999991611392`
# there; `123456789012345678.5` to 0 is `123456789012345678` here,
# `123456789012345680` there) and past the double's range (`1e400` is written
# out in full here, `inf` there). Exact values agree (`0.125`, `2.5` to 0
# places is `2`, `0.5` is `0`). The steps are stated over `src/fixed.bend`, in
# the order the text is read: the sign (laws/FixedKeepsMinus.bend), the cut
# and the exponent (laws/FixedSplitsMantissaAndExponent.bend), the rounding
# (laws/FixedRoundsHalfToEven.bend), the writing
# (laws/FixedWritesDigits.bend); together they define the result for every
# text. The exponent is read as a natural number and the point moved one place
# a step, so the time and memory of a call grow with the exponent's value:
# `1e999999999` asks for a billion digits, and a caller formatting untrusted
# numbers bounds the exponent first.
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ../src/fixed.bend as F

# LAW: num.fixed of a text that is not a JSON number is None
law fixed_none:
  for +txt: String
  for +nn: Nat
  for +h: {V.num.ok(txt) == False{} : Bool}
  {Ezjson.num.fixed(txt, nn) == None{} : Maybe<&2, String>}

# LAW: num.fixed of a JSON number is Some of its text with nn decimals
law fixed_some:
  for +txt: String
  for +nn: Nat
  for +h: {V.num.ok(txt) == True{} : Bool}
  {Ezjson.num.fixed(txt, nn) == Some{F.text(txt, nn)} : Maybe<&2, String>}
