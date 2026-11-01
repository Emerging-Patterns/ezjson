# `num(s)` is `JNum{s}` when `num.ok(s)`, and `null()` otherwise
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson

# LAW: num of a JSON number keeps its text
law num_keeps:
  for +txt: String
  for h_ok: {V.num.ok(txt) == True{} : Bool}
  {Ezjson.num(txt) == V.JNum{txt} : V.Json}

# LAW: num of any other text is null
law num_null:
  for +txt: String
  for h_bad: {V.num.ok(txt) == False{} : Bool}
  {Ezjson.num(txt) == Ezjson.null() : V.Json}
