# For texts shorter than 2^32 - 1 characters: a bare word parses exactly when
# it is `null`, `true`, `false` or a number, and the literals are only the
# lowercase words (§3)
import Base
import ../main.bend as Ezjson
import ./defs/CursorAndNumberRules.bend as D1

# LAW: a bare word parses exactly when it is null, true, false or a number
law bare_word:
  for +txt: String
  for h_b: {D1.bare(txt) == True{} : Bool}
  for h_s: {D1.short(txt) == True{} : Bool}
  {D1.is_some(Ezjson.parse(txt)) == D1.lit_or_num(txt) : Bool}
