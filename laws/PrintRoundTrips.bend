# For texts shorter than 2^32 - 1 characters: for every well-formed value `j`,
# `parse(print(j))` is `Some` of a value `same` as `j` with every code point
# that is not a Unicode scalar value replaced by U+FFFD
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ./defs/CursorAndNumberRules.bend as D1

# LAW: print then parse gives back a value `same` as the one printed, with
# every code point that is not a Unicode scalar value replaced by U+FFFD
law print_parse:
  for +val: V.Json
  for +h_wf: {V.wf(val) == True{} : Bool}
  for h_s: {D1.short(Ezjson.print(val)) == True{} : Bool}
  {D1.own_m(Ezjson.parse(Ezjson.print(val))) == Some{D1.fixv(D1.own(val))} : Maybe<&2, V.Json>}
