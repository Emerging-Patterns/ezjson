# For texts shorter than 2^32 - 1 characters: for every text `t`, `parse` of
# U+FEFF followed by `t` is `None` (§8.1)
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ./defs/CursorAndNumberRules.bend as D1

# LAW: a text that starts with U+FEFF, a byte order mark, does not parse
law bom_none:
  for +txt: String
  for h_s: {D1.short(SCon{Char.from_u32(65279), txt}) == True{} : Bool}
  {Ezjson.parse(SCon{Char.from_u32(65279), txt}) == None{} : Maybe<&2, V.Json>}
