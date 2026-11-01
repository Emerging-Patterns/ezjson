# `as_bool(bool(b)) == Some{b}`, `as_str(str(s)) == Some{s}`, and
# `as_num(num(s)) == Some{s}` when `num.ok(s)`
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson

# LAW: as_bool reads back the boolean bool built
law as_bool_bool:
  for flag: Bool
  {Ezjson.as_bool(Ezjson.bool(flag)) == Some{flag} : Maybe<&2, Bool>}

# LAW: as_str reads back the string str built
law as_str_str:
  for txt: String
  {Ezjson.as_str(Ezjson.str(txt)) == Some{txt} : Maybe<&2, String>}

# LAW: as_num reads back the text num built from a JSON number
law as_num_num:
  for +txt: String
  for h_ok: {V.num.ok(txt) == True{} : Bool}
  {Ezjson.as_num(Ezjson.num(txt)) == Some{txt} : Maybe<&2, String>}
