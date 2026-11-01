# For every text `s` and count `n`, the text of `-` followed by `s` is `-`
# followed by the unsigned text of `s`, and a text that does not start with
# `-` (the empty one too) is written unsigned: the minus is kept even when
# every digit rounds to `0`, so `-0.04` to 1 place is `-0.0` and `-0` to 2 is
# `-0.00`, as Python's `'%.Nf'` and C's `printf` write a negative zero
import Base
import ../src/fixed.bend as F

# LAW: a leading minus is written, then the rest unsigned, whatever the
# digits round to
law text_minus:
  for +txt: String
  for +nn: Nat
  {F.text("-" ++ txt, nn) == "-" ++ F.unsigned(txt, nn) : String}

# LAW: a text that starts with anything but a minus is written unsigned
law text_plain:
  for +ch: Char
  for +tl: String
  for +nn: Nat
  for +h: {Char.is_eq(ch, '-') == False{} : Bool}
  {F.text(SCon{ch, tl}, nn) == F.unsigned(SCon{ch, tl}, nn) : String}

# LAW: the empty text is written unsigned
law text_empty:
  for +nn: Nat
  {F.text("", nn) == F.unsigned("", nn) : String}
