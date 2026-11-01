# For texts shorter than 2^32 - 1 characters: for every `s` with `num.ok(s)`,
# `parse(s)` is `Some{JNum{s}}` and `print` of it is `s`: a number keeps its
# spelling
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ./defs/CursorAndNumberRules.bend as D1

# LAW: a JSON number parses as itself, spelling kept
law parse_num:
  for +raw: String
  for h_ok: {V.num.ok(raw) == True{} : Bool}
  for h_s: {D1.short(raw) == True{} : Bool}
  {Ezjson.parse(raw) == Some{V.JNum{raw}} : Maybe<&2, V.Json>}

# LAW: a number prints as its spelling
law print_num:
  for +raw: String
  {Ezjson.print(V.JNum{raw}) == raw : String}
