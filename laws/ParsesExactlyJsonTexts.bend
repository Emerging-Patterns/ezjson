# For texts shorter than 2^32 - 1 characters, all of them code points (at most
# U+10FFFF): `parse(t)` is `Some` exactly when `t` matches RFC 8259's
# `JSON-text` rule (§2 to §7) and holds no `\u` escape of an unpaired
# surrogate (§8.2)
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ./defs/CursorAndNumberRules.bend as D1
import ./defs/GrammarDerivations.bend as D2

# a literal name or a number as a value
def g.word(+txt: String) -> V.Json:
  Bool.pick(V.Json, String.eq(txt, "null"), V.JNull{},
    Bool.pick(V.Json, String.eq(txt, "true"), V.JBool{True{}},
      Bool.pick(V.Json, String.eq(txt, "false"), V.JBool{False{}}, V.JNum{txt})))

# the value a derivation stands for, strings decoded
def g.val(gg: D2.Gv) -> V.Json:
  match gg:
    case D2.GWord{w}:
      g.word(w)
    case D2.GStr{ps}:
      V.JStr{D2.spelled(ps)}
    case D2.GArr0{_}:
      V.JArr{V.JNil{}}
    case D2.GArr{_, vv, _, rr}:
      V.JArr{V.JCons{g.val(vv), g.val(rr)}}
    case D2.GObj0{_}:
      V.JObj{V.JNil{}}
    case D2.GObj{_, ps, _, _, vv, _, rr}:
      V.JObj{V.JPair{D2.spelled(ps), g.val(vv), g.val(rr)}}
    case D2.GEnd{}:
      V.JNil{}
    case D2.GNext{_, vv, _, rr}:
      V.JCons{g.val(vv), g.val(rr)}
    case D2.GNextM{_, ps, _, _, vv, _, rr}:
      V.JPair{D2.spelled(ps), g.val(vv), g.val(rr)}

# LAW: a text RFC 8259's JSON-text rule derives, whitespace, a value and
# whitespace, parses, as the value the derivation stands for
law text_some:
  for +gg: D2.Gv
  for +wa: String
  for +wb: String
  for +h_g: {D2.g.ok(gg, D2.GKVal{}) == True{} : Bool}
  for +h_a: {D1.all_ws(wa) == True{} : Bool}
  for +h_b: {D1.all_ws(wb) == True{} : Bool}
  for h_s: {D1.short(wa ++ D2.g.text(gg) ++ wb) == True{} : Bool}
  {D1.own_m(Ezjson.parse(wa ++ D2.g.text(gg) ++ wb)) == Some{g.val(gg)} : Maybe<&2, V.Json>}

# LAW: a text that parses is RFC 8259's JSON-text rule: whitespace, a
# derivation's text and whitespace
law text_derives:
  for +txt: String
  for +h_s: {D1.short(txt) == True{} : Bool}
  for +h_p: {D1.is_some(Ezjson.parse(txt)) == True{} : Bool}
  exs wa: String
  exs gg: D2.Gv
  exs wb: String
  ({txt == wa ++ D2.g.text(gg) ++ wb : String} & {D2.derived(wa, gg, wb) == True{} : Bool})
