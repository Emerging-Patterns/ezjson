# For texts shorter than 2^32 - 1 characters: for every string `s` of Unicode
# scalar values, `parse(quote(s))` is a string value whose characters are `s`
# (§7)
import Base
import ../main.bend as Ezjson
import ./defs/CursorAndNumberRules.bend as D1

# LAW: a printed string of scalar values parses back as a string of the same
# characters
law str_back:
  for +txt: String
  for h_sc: {D1.scalars(txt) == True{} : Bool}
  for h_s: {D1.short(Ezjson.print(Ezjson.str(txt))) == True{} : Bool}
  {D1.str_of(Ezjson.parse(Ezjson.print(Ezjson.str(txt)))) == Some{txt} : Maybe<&2, String>}
