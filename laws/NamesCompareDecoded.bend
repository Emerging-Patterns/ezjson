# For texts shorter than 2^32 - 1 characters: two object names compare equal
# in `get` exactly when their decoded characters are equal, whatever escapes
# spelled them (§8.3)
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ./defs/CursorAndNumberRules.bend as D1
import ./defs/GrammarDerivations.bend as D2

# get on a parsed value, with the value found read out as owned strings
def get_m(mb: Maybe<&2, V.Json>, +key: String) -> Maybe<&2, V.Json>:
  match mb:
    case None{}:
      None{}
    case Some{jj}:
      Some{D1.own(Ezjson.get(jj, key))}

# LAW: get finds an object's member exactly when the key is the characters
# the member's name decodes to, whatever escapes spell it
law get_decoded:
  for +ps: List<&2, D2.Piece>
  for +val: V.Json
  for +key: String
  for +h_ok: {D2.spell_ok(ps) == True{} : Bool}
  for +h_sc: {D1.scalars(D2.spelled(ps)) == True{} : Bool}
  for +h_wf: {V.wf(val) == True{} : Bool}
  for h_s: {D1.short("{\"" ++ D2.spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}") == True{} : Bool}
  {get_m(Ezjson.parse("{\"" ++ D2.spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}"), key) ==
    Some{Bool.pick(V.Json, String.eq(D2.spelled(ps), key), D1.fixv(D1.own(val)), V.JNull{})} : Maybe<&2, V.Json>}
