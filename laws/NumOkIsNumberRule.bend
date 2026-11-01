# `num.ok(s)` holds exactly when `s` matches RFC 8259's `number` rule: an
# optional `-`, `0` or a nonzero digit and digits, an optional `.` and one or
# more digits, an optional `e` or `E`, an optional sign and one or more digits
# (§6)
import Base
import ../src/value.bend as V
import ./defs/CursorAndNumberRules.bend as D1

# LAW: num.ok holds of a text exactly when it matches RFC 8259's number rule
law num_grammar:
  for +txt: String
  {V.num.ok(txt) == D1.number(String.to_list(txt)) : Bool}
